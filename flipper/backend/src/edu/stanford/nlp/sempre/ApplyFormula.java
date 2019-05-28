package edu.stanford.nlp.sempre;

import java.util.List;
import java.util.LinkedList;

import com.google.common.base.Function;

import fig.basic.LispTree;

public class ApplyFormula extends Formula {

  public final Formula lambda;
  public final Formula arg;
  
  public ApplyFormula(Formula lambda, Formula arg) {
    this.lambda = lambda;
    this.arg = arg;
  }

  @Override
  public LispTree toLispTree() {
    LispTree tree = LispTree.proto.newList();
    tree.addChild("apply");
    tree.addChild(lambda.toLispTree());
    tree.addChild(arg.toLispTree());
    return tree;
  }

  @Override
  public void forEach(Function<Formula, Boolean> func) {
    throw new RuntimeException("Not yet implemented");
    // TODO Auto-generated method stub
    
  }

  @Override
  public Formula map(Function<Formula, Formula> func) {
    Formula result = func.apply(this);
    return result == null ? new ApplyFormula(lambda.map(func), arg/*.map(func)*/) : result;
  }

  @Override
  public List<Formula> mapToList(Function<Formula, List<Formula>> func, boolean alwaysRecurse) {
    // TODO Auto-generated method stub
    throw new RuntimeException("Not yet implemented");
  }

  @Override
  public boolean equals(Object o) {
    throw new RuntimeException("Not yet implemented");
    // TODO Auto-generated method stub
  }

  @Override
  public int computeHashCode() {
    throw new RuntimeException("Not yet implemented");
    // TODO Auto-generated method stub
  }
  
  @Override
  public List<Formula>getChildren(){
	 
	  LinkedList children = new LinkedList();
	  children.add(this.arg);
	  return children;
	  
  }


}
