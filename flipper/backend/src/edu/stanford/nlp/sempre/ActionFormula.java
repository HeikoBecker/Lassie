package edu.stanford.nlp.sempre;

import java.util.List;
import java.util.stream.Collectors;

import com.google.common.base.Function;
import com.google.common.collect.Lists;

import fig.basic.LispTree;
import fig.basic.LogInfo;

/**
 * An ActionFormula represent a compositional action used in the interactive
 * package : is used as a prefix to denote an ActionFormula primitive (:
 * actioname args) sequential (:s ActionFormula ActionFormula ...) repeat (:loop
 * Number ActionFormula) conditional (:if Set ActionFormula) block scoping (:blk
 * ActionFormula)
 * 
 * @author sidaw
 */
public class ActionFormula extends Formula {
  public enum Mode {
    primitive(":"), // (: remove *)
    sequential(":s"), // (:s (: add red top) (: remove this))
    repeat(":loop"), // (:loop (count (has color green)) (: add red top))
    conditional(":if"), // (:if (count (has color green)) (: add red top))
    whileloop(":while"), // (:while (count (has color green)) (: add red top))
    forset(":for"), // (:for (and this (color red)) (:s (: add red top) (: add
                    // yellow top) (: remove)))
    foreach(":foreach"), 
    realizable(":realizable"), 
    strict(":strict"), 

    // primitives for declaring variables
    // let(":let"), // (:let X *),
    // set(":set"), // (:set X *)

    block(":blk"), // start a block of code (like {}) with a new scope
    blockr(":blkr"), // also return a result after finishing the block
    isolate(":isolate"),
    other(":?");

    private final String value;

    Mode(String value) {
      this.value = value;
    }

    @Override
    public String toString() {
      return this.value;
    }
  };

  public final Mode mode;
  public final List<Formula> args;

  public ActionFormula(Mode mode, List<Formula> args) {
    this.mode = mode;
    this.args = args;
  }
  
  @Override
  public String prettyString(){
	  String s;
	  if (this.mode.equals(Mode.primitive)){
		  if (this.getChildren().get(0).prettyString().equals("itemActionHandler")){
			  s = this.getChildren().get(1).prettyString() + " "+this.getChildren().get(2).prettyString();
		  }
		  else if(this.getChildren().get(0).prettyString().equals("visit") || 
				  this.getChildren().get(0).prettyString().equals("visitAreaCollections") ||
				  this.getChildren().get(0).prettyString().equals("visitArea")){
			  if (this.getChildren().size() == 3){
				  s = "visit "+this.getChildren().get(1).prettyString() + " while avoiding "+this.getChildren().get(2).prettyString();
			  }
			  else
			  {
				  s = "visit "+this.getChildren().get(1).prettyString();
			  }
		  }
		  else {
			  s = this.getChildren().get(0).prettyString() + " "+this.getChildren().get(1).prettyString();
		  }
		  
	  }
	  else if (this.mode.equals(Mode.foreach)){
		  s = "foreach "+this.getChildren().get(0).prettyString() + " in "+this.getChildren().get(1).prettyString() + " "+this.getChildren().get(2).prettyString();
	  }
	  else if (this.mode.equals(Mode.conditional)){
		  s = "if "+this.getChildren().get(0).prettyString() + " "+this.getChildren().get(1).prettyString();
	  }
	  else if (this.mode.equals(Mode.realizable)){
		  s = "possible "+this.getChildren().get(0).prettyString();
	  }
	  else if (this.mode.equals(Mode.strict)){
		  s = "strict "+this.getChildren().get(0).prettyString();
	  }
	  else if (this.mode.equals(Mode.whileloop)){
		  s = "while "+this.getChildren().get(0).prettyString()+" "+this.getChildren().get(1).prettyString();
	  }
	  else if (this.mode.equals(Mode.sequential)){
		  String joined = this.getChildren().stream()
				  							 .map(c -> c.prettyString())
				  							 .collect(Collectors.joining(";"));
		  s = joined;
		  
	  }
	  else if (this.mode.equals(Mode.repeat)){
		  s = "repeat "+this.getChildren().get(0).prettyString()+" times "+this.getChildren().get(1).prettyString();
	  }
	  else {
		  s = this.toString();
	  }
	  if (precisePrettyPrinting){
		  return "{"+s+"}";
	  }
	  else{
		  return s;
	  }
  }
  
  @Override
  public List<Formula>getChildren(){
	 
	  return this.args;
	  
  }

  public static Mode parseMode(String mode) {
    if (mode == null)
      return null;
    for (Mode m : Mode.values()) {
      // LogInfo.logs("mode string %s \t== %s \t!= %s", m.toString(), mode,
      // m.name());
      if (m.toString().equals(mode))
        return m;
    }
    if (mode.startsWith(":"))
      throw new RuntimeException("Unsupported ActionFormula mode");
    return null;
  }

  @Override
  public LispTree toLispTree() {
    LispTree tree = LispTree.proto.newList();
    tree.addChild(this.mode.toString());
    for (Formula arg : args)
      tree.addChild(arg.toLispTree());
    return tree;
  }

  @Override
  public void forEach(Function<Formula, Boolean> func) {
    if (!func.apply(this)) {
      for (Formula arg : args)
        arg.forEach(func);
    }
  }

  @Override
  public Formula map(Function<Formula, Formula> transform) {
    Formula result = transform.apply(this);
    if (result != null)
      return result;
    List<Formula> newArgs = Lists.newArrayList();
    for (Formula arg : args)
      newArgs.add(arg.map(transform));
    return new ActionFormula(this.mode, newArgs);
  }

  @Override
  public List<Formula> mapToList(Function<Formula, List<Formula>> transform, boolean alwaysRecurse) {
    List<Formula> res = transform.apply(this);
    if (res.isEmpty() || alwaysRecurse) {
      for (Formula arg : args)
        res.addAll(arg.mapToList(transform, alwaysRecurse));
    }
    return res;
  }

  @SuppressWarnings({ "equalshashcode" })
  @Override
  public boolean equals(Object thatObj) {
    if (!(thatObj instanceof ActionFormula))
      return false;
    ActionFormula that = (ActionFormula) thatObj;
    if (!this.mode.equals(that.mode))
      return false;
    if (!this.args.equals(that.args))
      return false;
    return true;
  }

  @Override
  public int computeHashCode() {
    int hash = 0x7ed55d16;
    hash = hash * 0xd3a2646c + mode.hashCode();
    hash = hash * 0xd3a2646c + args.hashCode();
    return hash;
  }
}
