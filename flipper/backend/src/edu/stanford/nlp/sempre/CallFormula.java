package edu.stanford.nlp.sempre;

import com.google.common.base.Function;
import com.google.common.collect.Lists;
import fig.basic.LispTree;
import fig.basic.LogInfo;
import java.util.List;

/**
 * A CallFormula represents a function call.
 * See JavaExecutor for the semantics of this formula.
 *   (call func arg_1 ... arg_k)
 *
 * @author Percy Liang
 */
public class CallFormula extends Formula {
  public final Formula func;
  public final List<Formula> args;
  

  public CallFormula(String func, List<Formula> args) {
    this(Formulas.newNameFormula(func), args);
  }

  public CallFormula(Formula func, List<Formula> args) {
    this.func = func;
    this.args = args;
  }

  @Override
  public List<Formula>getChildren(){
	
	  return this.args;
	  
  }
  
  
  @Override
  public String prettyString(){
	  String s;
	if (this.func.toString().equals( "makePoint" )){
		s = "[" + this.args.get(0).prettyString() + ","+this.args.get(1).prettyString()+"]"; 
	} 
	else if (this.func.toString().equals("anyPoint")){
		s = "{any point in "+this.args.get(0).prettyString()+"}";
	}
	else if (this.func.toString().equals("getAreaWithCorners")){
		s = "area with corners "+this.args.get(0).prettyString()+" and "+this.args.get(1).prettyString();
		if (precisePrettyPrinting) {
			s = "{" + s + "}";
		}
	}
	else if (this.func.toString().equals("anyArea")){
		
		s = "any area in "+this.args.get(0).prettyString();
		if (precisePrettyPrinting) {
			s = "{" + s + "}";
		}
	}
	else if (this.func.toString().equals("createAreaListFromArea")){
		s = this.args.get(0).prettyString();
	}
	else if (this.func.toString().equals("combineCollections") || this.func.toString().equals("combineAreas")){
		s = this.args.get(0).prettyString() + ", "+this.args.get(1).prettyString();
	}
	else if (this.func.toString().equals("makeArray")){
		s = "["+this.args.get(0).prettyString() +"]";
		if (precisePrettyPrinting) {
			s = "{" + s + "}";
		}

	}
	else if (this.func.toString().equals("roomsComplement")) {
		String p = this.args.get(0).prettyString();
		
		s = "not  "+p;
		if (precisePrettyPrinting) {
			s = "{" + s + "}";
		}
				
	}
	else if (this.func.toString().equals("roomsFromItems")){
		s = this.args.get(0).prettyString() + " containing item "+this.args.get(1).prettyString();
		if (precisePrettyPrinting){
			s = "{" + s + "}";
		}
	}
	else if (this.func.toString().equals("areasFromItems")){
		s = this.args.get(0).prettyString() + " containing item "+this.args.get(1).prettyString();
		if (precisePrettyPrinting){
			s = "{" + s + "}";
		}
	}
	else if (this.func.toString().equals("pointsFromItems")){
		s = "world containing item "+this.args.get(0).prettyString();
		if (precisePrettyPrinting){
			s = "{" + s + "}";
		}
	}
	else if (this.func.toString().equals("filterArea")){
		s = this.args.get(0).prettyString() +" containing item "+this.args.get(1).prettyString();
		if (precisePrettyPrinting){
			s = "{" + s + "}";
		}
	}
	else if (this.func.toString().equals("robotHas")){
		s = "robot has item "+this.args.get(0).prettyString();
		if (precisePrettyPrinting){
			s = "{" + s + "}";
		}
		
	}
	else if (this.func.toString().equals("setOfLocationsDifference")){
		s = this.args.get(0).prettyString() + " minus "+this.args.get(1).prettyString();
		if (precisePrettyPrinting){
			s = "{" + s + "}";
		}
		
	}
	else if (this.func.toString().equals("itemAt")){
		s = "item at "+this.args.get(0).prettyString() + this.args.get(1).prettyString();
		if (precisePrettyPrinting){
			s = "{" + s + "}";
		}
	}
	else if (this.func.toString().equals("getRobotLocation")){
		s = "current";
	}
	else if (this.func.toString().equals("robotAt")){
		s = "robot at "+this.args.get(0).prettyString();
		if (precisePrettyPrinting){
			s = "{" + s + "}";
		}
	}
	else if (this.func.toString().equals("filterCollection")){
		s = this.args.get(0).prettyString() +" containing item "+this.args.get(1).prettyString();
		if (precisePrettyPrinting){
			s = "{" + s + "}";
		}
	}
	else if (this.func.toString().equals("getSelectedPoint")){
		s = "point";
	}
	else if (this.func.toString().equals("getSelectedArea")){
		s = "area";
	}
	else if (this.func.toString().equals("setLimit")){
		s = "";
		if (this.args.get(0).prettyString().equals("-1.0")){
			s = "every item "+this.args.get(1).prettyString();
		}
		else if (this.args.get(0).prettyString().equals("1.0")){
			s = "item "+this.args.get(1).prettyString();
		}
	}
	else if (this.func.toString().equals("allItems")){
		s = "";
		
	}
	else {
		s = this.toString();
	}
	return s;
  }
  
  public LispTree toLispTree() {
    LispTree tree = LispTree.proto.newList();
    tree.addChild("call");
    tree.addChild(func.toLispTree());
    for (Formula arg : args)
      tree.addChild(arg.toLispTree());
    return tree;
  }

  @Override
  public void forEach(Function<Formula, Boolean> func) {
    if (!func.apply(this)) {
      this.func.forEach(func);
      for (Formula arg: args)
        arg.forEach(func);
    }
  }

  @Override
  public Formula map(Function<Formula, Formula> transform) {
    Formula result = transform.apply(this);
    if (result != null) return result;
    Formula newFunc = func.map(transform);
    List<Formula> newArgs = Lists.newArrayList();
    for (Formula arg : args)
      newArgs.add(arg.map(transform));
    return new CallFormula(newFunc, newArgs);
  }

  @Override
  public List<Formula> mapToList(Function<Formula, List<Formula>> transform, boolean alwaysRecurse) {
    List<Formula> res = transform.apply(this);
    if (res.isEmpty() || alwaysRecurse) {
      res.addAll(func.mapToList(transform, alwaysRecurse));
      for (Formula arg : args)
        res.addAll(arg.mapToList(transform, alwaysRecurse));
    }
    return res;
  }

  @SuppressWarnings({"equalshashcode"})
  @Override
  public boolean equals(Object thatObj) {
    if (!(thatObj instanceof CallFormula)) return false;
    CallFormula that = (CallFormula) thatObj;
    if (!this.func.equals(that.func)) return false;
    if (!this.args.equals(that.args)) return false;
    return true;
  }

  public int computeHashCode() {
    int hash = 0x7ed55d16;
    hash = hash * 0xd3a2646c + func.hashCode();
    hash = hash * 0xd3a2646c + args.hashCode();
    return hash;
  }
}
