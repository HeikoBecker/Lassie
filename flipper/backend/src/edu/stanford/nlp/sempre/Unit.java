package edu.stanford.nlp.sempre;

import java.util.HashSet;
import java.util.Set;

/**
 * A proper unit type (a la Scala)
 * @author brendonboldt
 * This is used when sets are used a booleans. The reason that Set<Unit> is
 * useful is because it makes the complement of the empty set easy to generate.
 */
public final class Unit {
  
  private static Unit instance = new Unit();
  
  public static Unit get() { return instance; }
  
  public static Set<Unit>  trueSet() {
    Set<Unit> s = new HashSet<>();
    s.add(instance);
    return s;
  }
  
  public static TypedEmptySet falseSet() {
    return new TypedEmptySet(Unit.class);
  }
  
  private Unit() { }
}
