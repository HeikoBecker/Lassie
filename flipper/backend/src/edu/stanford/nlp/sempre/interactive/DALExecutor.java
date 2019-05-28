package edu.stanford.nlp.sempre.interactive;

import java.awt.Point;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import com.google.common.collect.Lists;
import com.google.common.collect.Sets;
import com.google.common.collect.Sets.SetView;

import edu.stanford.nlp.sempre.ActionFormula;
import edu.stanford.nlp.sempre.AggregateFormula;
import edu.stanford.nlp.sempre.ApplyFormula;
import edu.stanford.nlp.sempre.ArithmeticFormula;
import edu.stanford.nlp.sempre.BooleanValue;
import edu.stanford.nlp.sempre.CallFormula;
import edu.stanford.nlp.sempre.ContextValue;
import edu.stanford.nlp.sempre.ErrorValue;
import edu.stanford.nlp.sempre.Executor;
import edu.stanford.nlp.sempre.Formula;
import edu.stanford.nlp.sempre.Formulas;
import edu.stanford.nlp.sempre.JoinFormula;
import edu.stanford.nlp.sempre.LambdaFormula;
import edu.stanford.nlp.sempre.LimitFormula;
import edu.stanford.nlp.sempre.ListValue;
import edu.stanford.nlp.sempre.MergeFormula;
import edu.stanford.nlp.sempre.NameValue;
import edu.stanford.nlp.sempre.NotFormula;
import edu.stanford.nlp.sempre.NumberValue;
import edu.stanford.nlp.sempre.ReverseFormula;
import edu.stanford.nlp.sempre.StringValue;
import edu.stanford.nlp.sempre.SuperlativeFormula;
import edu.stanford.nlp.sempre.TypedEmptySet;
import edu.stanford.nlp.sempre.Unit;
import edu.stanford.nlp.sempre.Value;
import edu.stanford.nlp.sempre.ValueFormula;
import edu.stanford.nlp.sempre.interactive.planner.PathFinder;
import edu.stanford.nlp.sempre.interactive.robolurn.RoboWorld;
import fig.basic.LogInfo;
import fig.basic.Option;

/**
 * Handles action lambda DCS where the world has a flat structure, i.e. a list
 * of allitems all supporting the same operations supports ActionFormula here,
 * and does conversions of singleton sets
 * 
 * @author sidaw
 */
public class DALExecutor extends Executor {
  public static class Options {
    @Option(gloss = "Whether to convert NumberValue to int/double")
    public boolean convertNumberValues = true;
    @Option(gloss = "Whether to convert name values to string literal")
    public boolean convertNameValues = true;

    @Option(gloss = "Print stack trace on exception")
    public boolean printStackTrace = false;
    // the actual function will be called with the current ContextValue as its
    // last argument if marked by contextPrefix
    @Option(gloss = "Reduce verbosity by automatically appending, for example, edu.stanford.nlp.sempre to java calls")
    public String classPathPrefix = "edu.stanford.nlp.sempre";

    @Option(gloss = "The type of world used")
    public String worldType = "RoboWorld";
    //public String worldType = "VoxelWorld";

    @Option(gloss = "the maximum number of primitive calls until we stop executing")
    public int maxSteps = 1000;

    @Option(gloss = "The maximum number of while calls")
    public int maxWhile = 20;
    
    @Option(gloss = "Verbosity")
    public int verbose = 0;
  }

  public static Options opts = new Options();

  public RoboWorld worldAfterExecution(Formula formula, ContextValue context){
	  RoboWorld world = (RoboWorld)World.fromContext(opts.worldType, context);
	  formula = Formulas.betaReduction(formula);
	  performActions((ActionFormula)formula, world);
	  return world;
  }
  
  @Override
  public Response execute(Formula formula, ContextValue context) {
    // We can do beta reduction here since macro substitution preserves the
    // denotation (unlike for lambda DCS).
    //World world = World.fromContext(opts.worldType, context);

    //LogInfo.logs(context.toString());
    World world = World.fromContext(opts.worldType, context);
    formula = Formulas.betaReduction(formula);
    try {
      performActions((ActionFormula) formula, world);
      //return new Response(new StringValue(world.toJSON()));
      return new Response(new StringValue(world.getJSONResponse()));
    } catch (Exception e) {
      // Comment this out if we expect lots of innocuous type checking failures
      if (opts.printStackTrace) {
        LogInfo.log("Failed to execute " + formula.toString());
        e.printStackTrace();
      }
      return new Response(ErrorValue.badJava(e.toString()));
    }
  }
  
  
  // Return whether that action was able to be realized
  @SuppressWarnings("rawtypes")
  private boolean performActions(ActionFormula f, final World world) {
    if (opts.verbose >= 1) {
      LogInfo.begin_track("DALExecutor.performActions");
      LogInfo.logs("Executing: %s", f);
      LogInfo.logs("World: %s", world.toJSON());
      LogInfo.end_track();
    }
    if (f.mode == ActionFormula.Mode.primitive) {
      // use reflection to call primitive stuff
      Value method = ((ValueFormula) f.args.get(0)).value;
      String id = ((NameValue) method).id;
      // all actions takes a fixed set as argument
      boolean result = invokeAction(
          id,
          world,
          f,
          f.args.subList(1, f.args.size()).stream().map(x -> processSetFormula(x, world)).toArray());
      return result;
      //world.merge();
    } else if (f.mode == ActionFormula.Mode.sequential) {
      boolean successful = true;
      for (Formula child : f.args) {
        successful &= performActions((ActionFormula) child, world);
      }
      return successful;
    } else if (f.mode == ActionFormula.Mode.repeat) {
      Set<Object> arg = toSet(processSetFormula(f.args.get(0), world));
      if (arg.size() > 1)
        throw new RuntimeException("repeat has to take a single number");
      int times;
      if (!opts.convertNumberValues)
        times = (int) ((NumberValue) arg.iterator().next()).value;
      else
        times = (int) arg.iterator().next();

      boolean successful = true;
      for (int i = 0; i < times; i++)
        successful &= performActions((ActionFormula) f.args.get(1), world);
      return successful;
    } else if (f.mode == ActionFormula.Mode.conditional) {
      // using the empty set to represent false
      // The combination of "robot has" and "not" does not work
      //System.out.printf("~~~ %s\n", toSet(processSetFormula(f.args.get(0), world)));
      boolean cond = toSet(processSetFormula(f.args.get(0), world)).iterator().hasNext();
      boolean successful = true;
      if (cond)
        successful &= performActions((ActionFormula) f.args.get(1), world);
      return successful;
    } else if (f.mode == ActionFormula.Mode.whileloop) {
      // using the empty set to represent false
      boolean cond = toSet(processSetFormula(f.args.get(0), world)).iterator().hasNext();
      boolean successful = true;
      for (int i = 0; i < opts.maxWhile; i++) {
        if (cond)
          successful &= performActions((ActionFormula) f.args.get(1), world);
        else
          break;
        cond = toSet(processSetFormula(f.args.get(0), world)).iterator().hasNext();
      }
      return successful;
    } else if (f.mode == ActionFormula.Mode.forset) {
      return performActions((ActionFormula) f.args.get(1), world);
    } else if (f.mode == ActionFormula.Mode.foreach) {
      // Check whether the loop variable is `point` or `area`
      if ("point".equals(f.args.get(0).toString())) {
        List<Point> selected = toPointList(toSet(processSetFormula(f.args.get(1), world)));
        int[] order = PathFinder.getPointOrder(selected);
        boolean successful = true;
        for (int i = 0; i < order.length; ++i) {
          world.selectedPoint = Optional.of(selected.get(order[i]));
          successful &= performActions((ActionFormula) f.args.get(2), world);
        }
        world.selectedPoint = Optional.empty();
        return successful;
        
      } else if ("area".equals(f.args.get(0).toString())) {
        List<Set<Point>> selected = toAreaList(toSet(processSetFormula(f.args.get(1), world)));
        int[] order = PathFinder.getPointOrder(selected.stream()
            .filter(a -> !a.isEmpty())
            .map(a -> a.iterator().next()).collect(Collectors.toList()));
        boolean successful = true;
        for (int i = 0; i < order.length; ++i) {
          world.selectedArea = Optional.of(selected.get(order[i]));
          successful &= performActions((ActionFormula) f.args.get(2), world);
        }
        world.selectedArea = Optional.empty();
        return successful;
      } else {
        throw new RuntimeException(":foreach cannot be used with \"" + f.args.get(0) + "\", only with \"point\" and \"area\".");
      }
    } else if (f.mode == ActionFormula.Mode.strict) {
      World newWorld = world.clone();
      boolean successful = performActions((ActionFormula) f.args.get(0), newWorld);
      if (successful) {
        successful = performActions((ActionFormula) f.args.get(0), world);
      } else if (world instanceof RoboWorld) {
        ((RoboWorld) world).unrealizableStatus =
            ((RoboWorld) newWorld).unrealizableStatus;
      }
      return successful;
    } else {
      throw new RuntimeException("Unknown action.");
    }
  }

  @SuppressWarnings("unchecked")
  private Set<Object> toSet(Object maybeSet) {
    if (maybeSet instanceof Set)
      return (Set<Object>) maybeSet;
    else
      return Sets.newHashSet(maybeSet);
  }

  @SuppressWarnings("unused")
  private Point toPoint(int[] args) {
    Point p = new Point();
    p.x = args[0];
    p.y = args[1];
    return p;
  }
  
  private Object toElement(Set<Object> set) {
    if (set.size() == 1) {
      return set.iterator().next();
    }
    return set;
  }

  private Set<Block> toItemSet(Set<Object> maybeItems) {
    Set<Block> itemset = maybeItems.stream().map(i -> (Block) i).collect(Collectors.toSet());
    return itemset;
  }

  @SuppressWarnings({ "unused", "unchecked" })
  private Set<Point> toPointSet(Set<Object> maybePoints) {
    if (maybePoints.isEmpty())
      // This might cause a problem; return empty HashSet if so
      return (Set<Point>) new TypedEmptySet(Point.class);
    Set<Point> pointSet;
    if (maybePoints.iterator().next() instanceof Block)
      pointSet = maybePoints.stream().map(i -> ((Block) i).point).collect(Collectors.toSet());
    else
      pointSet = maybePoints.stream().map(i -> (Point) i).collect(Collectors.toSet());
    return pointSet;
  }

  @SuppressWarnings("unchecked")
  private List<Set<Point>> toAreaList(Set<Object> maybeAreas) {
    if (maybeAreas.isEmpty())
      return new ArrayList<>();
    List<Set<Point>> areaSet;
    areaSet = maybeAreas.stream().map(i -> ((Set<Point>) i)).collect(Collectors.toList());
    return areaSet;
  }

  private List<Point> toPointList(Set<Object> maybePoints) {
    if (maybePoints.isEmpty())
      return new ArrayList<>();
    List<Point> pointSet;
    if (maybePoints.iterator().next() instanceof Block)
      pointSet = maybePoints.stream().map(i -> ((Block) i).point).collect(Collectors.toList());
    else
      pointSet = maybePoints.stream().map(i -> (Point) i).collect(Collectors.toList());
    return pointSet;
  }


  static class SpecialSets {
//    static String World = "world";
//    static String AllItems = "allItems"; // Currently unused
//    static String Current = "current"; // Also unused
  };

  // a subset of lambda dcs. no types, and no marks
  // if this gets any more complicated, you should consider the
  // LambdaDCSExecutor
  @SuppressWarnings("unchecked")
  private Object processSetFormula(Formula formula, final World world) {
    if (formula instanceof ValueFormula<?>) {
      Value v = ((ValueFormula<?>) formula).value;
      // special unary
      if (v instanceof NameValue) {
        String id = ((NameValue) v).id;
        Set<? extends Object> set = world.getSpecialSet(id);
        if (set != null) // How should an undefined set be handled?
          return set;
      }
      return toObject(((ValueFormula<?>) formula).value);
    }

    if (formula instanceof JoinFormula) {
    	
      JoinFormula joinFormula = (JoinFormula) formula;
      if (joinFormula.relation instanceof ValueFormula) {
        String rel = ((ValueFormula<NameValue>) joinFormula.relation).value.id;
        Set<Object> unary = toSet(processSetFormula(joinFormula.child, world));
        
        return world.has(rel, unary);
      } else if (joinFormula.relation instanceof ReverseFormula) {
        ReverseFormula reverse = (ReverseFormula) joinFormula.relation;
        String rel = ((ValueFormula<NameValue>) reverse.child).value.id;
        Set<Object> unary = toSet(processSetFormula(joinFormula.child, world));
        // Untested
        return world.get(rel, toItemSet(unary));
      } else {
        throw new RuntimeException("relation can either be a value, or its reverse");
      }
    }

    if (formula instanceof MergeFormula) {
      MergeFormula mergeFormula = (MergeFormula) formula;
      MergeFormula.Mode mode = mergeFormula.mode;
      Set<Object> set1 = toSet(processSetFormula(mergeFormula.child1, world));
      Set<Object> set2 = toSet(processSetFormula(mergeFormula.child2, world));

      Set<Object> result;
      if (mode == MergeFormula.Mode.or)
        result = toMutable(Sets.union(set1, set2));
      else if (mode == MergeFormula.Mode.and)
        result = toMutable(Sets.intersection(set1, set2));
      else
        throw new RuntimeException("Unknown merge formula");

      if (result.isEmpty())
        return new TypedEmptySet(set1, set2);
      else
        return result;
    }

    if (formula instanceof NotFormula) {
      NotFormula notFormula = (NotFormula) formula;
      Set<Object> set1 = toSet(processSetFormula(notFormula.child, world));
      LogInfo.logs("set1 is %s with type %s", set1, set1.getClass());
      Iterator<Object> iter = set1.iterator();
      if (iter.hasNext()) {
        Object elem = iter.next();
        Set<? extends Object> result =
            toMutable(Sets.difference(world.universalSet(elem.getClass()), set1));
        if (result.isEmpty())
          return new TypedEmptySet(elem.getClass());
        else
          return result;
      } else if (set1 instanceof TypedEmptySet) {
        Set<? extends Object> result =
            toMutable(Sets.difference(world.universalSet(((TypedEmptySet) set1).type), set1));
        if (result.isEmpty())
          return set1; // Which is a TypedEmptySet
        return result;
      } else 
        throw new RuntimeException("Reverse formula cannot be executed on empty set.");
    }

    if (formula instanceof AggregateFormula) {
      AggregateFormula aggregateFormula = (AggregateFormula) formula;
      Set<Object> set = toSet(processSetFormula(aggregateFormula.child, world));
      AggregateFormula.Mode mode = aggregateFormula.mode;
      if (mode == AggregateFormula.Mode.count)
        return Sets.newHashSet(set.size());
      if (mode == AggregateFormula.Mode.max)
        return Sets.newHashSet(set.stream().max((s, t) -> ((NumberValue) s).value > ((NumberValue) t).value ? 1 : -1));
      if (mode == AggregateFormula.Mode.min)
        return Sets.newHashSet(set.stream().max((s, t) -> ((NumberValue) s).value < ((NumberValue) t).value ? 1 : -1));
    }

    if (formula instanceof ArithmeticFormula) {
      ArithmeticFormula arithmeticFormula = (ArithmeticFormula) formula;
      Integer arg1 = (Integer) processSetFormula(arithmeticFormula.child1, world);
      Integer arg2 = (Integer) processSetFormula(arithmeticFormula.child2, world);
      ArithmeticFormula.Mode mode = arithmeticFormula.mode;
      if (mode == ArithmeticFormula.Mode.add)
        return arg1 + arg2;
      if (mode == ArithmeticFormula.Mode.sub)
        return arg1 - arg2;
      if (mode == ArithmeticFormula.Mode.mul)
        return arg1 * arg2;
      if (mode == ArithmeticFormula.Mode.div)
        return arg1 / arg2;
    }

    if (formula instanceof CallFormula) {
      CallFormula callFormula = (CallFormula) formula;
      @SuppressWarnings("rawtypes")
      Value method = ((ValueFormula) callFormula.func).value;
      String id = ((NameValue) method).id;
      // all actions takes a fixed set as argument
      return invoke(id, world, callFormula.args.stream().map(x -> processSetFormula(x, world)).toArray());
    }
    
    if (formula instanceof ApplyFormula) {
      ApplyFormula applyFormula = (ApplyFormula) formula;
      if (applyFormula.lambda instanceof LambdaFormula) {
        Formula applied = Formulas.lambdaApply((LambdaFormula) applyFormula.lambda, applyFormula.arg);
        return processSetFormula(applied, world);
      } else
        throw new RuntimeException("First argument of ApplyFormula must be a LambdaFormula");
    }
    
    if (formula instanceof LimitFormula) {
      LimitFormula limitFormula = (LimitFormula) formula;
      Set<Object> arg = toSet(processSetFormula(limitFormula.number, world));
      if (arg.size() > 1)
        throw new RuntimeException("limit must take a single number");
      int limit;
      if (!opts.convertNumberValues)
        limit = (int) ((NumberValue) arg.iterator().next()).value;
      else
        limit = (int) arg.iterator().next();
      Set<Object> fullSet = toSet(processSetFormula(limitFormula.set, world));
      fullSet.removeIf(x -> fullSet.size() > limit);
      return fullSet;
    }
    
    if (formula instanceof ActionFormula) {
      ActionFormula actionFormula = (ActionFormula) formula;
      if (actionFormula.mode == ActionFormula.Mode.realizable) {
        if (performActions((ActionFormula) actionFormula.args.get(0), world.clone()))
          return Sets.newHashSet(Unit.get());
        else
          return new TypedEmptySet(Unit.class);
      } else {
        throw new RuntimeException(actionFormula + " cannot be treated as a set.");
      }
    }
    
    if (formula instanceof SuperlativeFormula) {
      throw new RuntimeException("SuperlativeFormula is not implemented");
    }
    throw new RuntimeException("ActionExecutor does not handle this formula type: " + formula.getClass());
  }
  
  private <T> Set<T> toMutable(SetView<T> intersection) {
    return new HashSet<>(intersection);
  }

  private boolean invokeAction(String id, World world, ActionFormula formula, Object... args) {
    ActionInterface ai = world.getActionInterface();
    Class<?> cls = ai.getClass();
    Method[] methods = cls.getMethods();
    String methodName = id;
    
    
    Object[] methodArgs = new Object[args.length + 1];
    methodArgs[0] = world;
    for (int i = 0; i < args.length; ++i) {
      methodArgs[i+1] = args[i];
    }

    // Find a suitable method
    List<Method> nameMatches = Lists.newArrayList();
    Method bestMethod = null;
    int bestCost = INVALID_TYPE_COST;
    for (Method m : methods) {
      if (!m.getName().equals(methodName))
        continue;
      m.setAccessible(true);
      nameMatches.add(m);
//      if (isStatic != Modifier.isStatic(m.getModifiers()))
//        continue;
      int cost = typeCastCost(m.getParameterTypes(), methodArgs);

      if (cost < bestCost) {
        bestCost = cost;
        bestMethod = m;
      }
    }

    if (bestMethod != null) {
    	
      try {
        Object result = bestMethod.invoke(ai, methodArgs);
        ai.handleActionResult(world, formula, result);
        return (boolean) result;
      } catch (InvocationTargetException e) {
        throw new RuntimeException(e.getCause());
      } catch (IllegalAccessException e) {
        throw new RuntimeException(e);
      }
    }

    List<String> types = Lists.newArrayList();
    for (Object arg : methodArgs)
          types.add(arg.getClass().toString());
        throw new RuntimeException("Method " + methodName + " not found in class " + cls + " with arguments "
            + Arrays.asList(methodArgs) + " having types " + types + "; candidates: " + nameMatches);
  }
  
  // Example: id = "Math.cos". similar to JavaExecutor's invoke,
  // but matches arg by building singleton set as needed
  private Object invoke(String id, World thisObj, Object... args) {
    Method[] methods;
    Class<?> cls;
    String methodName;
    boolean isStatic = thisObj == null;

    if (isStatic) { // Static methods
      int i = id.lastIndexOf('.');
      if (i == -1) {
        throw new RuntimeException("Expected <class>.<method>, but got: " + id);
      }
      String className = id.substring(0, i);
      methodName = id.substring(i + 1);

      try {
        cls = Class.forName(className);
      } catch (ClassNotFoundException e) {
        throw new RuntimeException(e);
      }
      methods = cls.getMethods();
    } else { // Instance methods
      cls = thisObj.getClass();
      methodName = id;
      methods = cls.getMethods();
    }

    // Find a suitable method
    List<Method> nameMatches = Lists.newArrayList();
    Method bestMethod = null;
    int bestCost = INVALID_TYPE_COST;
    for (Method m : methods) {
      if (!m.getName().equals(methodName))
        continue;
      m.setAccessible(true);
      nameMatches.add(m);
      if (isStatic != Modifier.isStatic(m.getModifiers()))
        continue;
      int cost = typeCastCost(m.getParameterTypes(), args);

      if (cost < bestCost) {
        bestCost = cost;
        bestMethod = m;
      }
    }

    if (bestMethod != null) {
      try {
        return bestMethod.invoke(thisObj, args);
      } catch (InvocationTargetException e) {
        throw new RuntimeException(e.getCause());
      } catch (IllegalAccessException e) {
        throw new RuntimeException(e);
      }
    }

    List<String> types = Lists.newArrayList();
    for (Object arg : args)
          types.add(arg.getClass().toString());
        throw new RuntimeException("Method " + methodName + " not found in class " + cls + " with arguments "
            + Arrays.asList(args) + " having types " + types + "; candidates: " + nameMatches);
  }

  @SuppressWarnings("unchecked")
  private int typeCastCost(Class<?>[] types, Object[] args) {
    if (types.length != args.length)
      return INVALID_TYPE_COST;
    int cost = 0;
    for (int i = 0; i < types.length; i++) {

      // deal with singleton sets
      if (types[i] == Set.class)
        args[i] = toSet(args[i]);
      if (types[i] != Set.class && args[i].getClass() == Set.class) {
        args[i] = toElement((Set<Object>) args[i]);
      }

      cost += typeCastCost(types[i], args[i]);
      if (cost >= INVALID_TYPE_COST) {
        // Brendon: Is this important to note?
        //LogInfo.dbgs("NOT COMPATIBLE: want %s, got %s with type %s", types[i], args[i], args[i].getClass());
        break;
      }
    }
    return cost;
  }

  private static Object toObject(Value value) {
    if (value instanceof NumberValue && opts.convertNumberValues) {
      // Unfortunately, NumberValues don't make a distinction between ints and
      // doubles, so this is a hack.
      double x = ((NumberValue) value).value;
      if (x == (int) x)
        return new Integer((int) x);
      return new Double(x);
    } else if (value instanceof NameValue && opts.convertNameValues) {
      String id = ((NameValue) value).id;
      return id;
    } else if (value instanceof BooleanValue) {
      return ((BooleanValue) value).value;
    } else if (value instanceof StringValue) {
      return ((StringValue) value).value;
    } else if (value instanceof ListValue) {
      List<Object> list = Lists.newArrayList();
      for (Value elem : ((ListValue) value).values)
        list.add(toObject(elem));
      return list;
    } else {
      return value; // Preserve the Value (which can be an object)
    }
  }

  // Return whether the object |arg| is compatible with |type|.
  // 0: perfect match
  // 1: don't match, but don't lose anything
  // 2: don't match, and can lose something
  // INVALID_TYPE_COST: impossible
  private int typeCastCost(Class<?> type, Object arg) {
    if (arg == null)
      return !type.isPrimitive() ? 0 : INVALID_TYPE_COST;
    if (type.isInstance(arg))
      return 0;
    if (type == Boolean.TYPE)
      return arg instanceof Boolean ? 0 : INVALID_TYPE_COST;
    else if (type == Integer.TYPE) {
      if (arg instanceof Integer)
        return 0;
      if (arg instanceof Long)
        return 1;
      return INVALID_TYPE_COST;
    }
    if (type == Long.TYPE) {
      if (arg instanceof Integer)
        return 1;
      if (arg instanceof Long)
        return 0;
      return INVALID_TYPE_COST;
    }
    if (type == Float.TYPE) {
      if (arg instanceof Integer)
        return 1;
      if (arg instanceof Long)
        return 1;
      if (arg instanceof Float)
        return 0;
      if (arg instanceof Double)
        return 2;
      return INVALID_TYPE_COST;
    }
    if (type == Double.TYPE) {
      if (arg instanceof Integer)
        return 1;
      if (arg instanceof Long)
        return 1;
      if (arg instanceof Float)
        return 1;
      if (arg instanceof Double)
        return 0;
      return INVALID_TYPE_COST;
    }
    return INVALID_TYPE_COST;
  }

  private static final int INVALID_TYPE_COST = 1000;
}
