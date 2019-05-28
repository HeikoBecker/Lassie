package edu.stanford.nlp.sempre;

import java.util.List;
import java.util.LinkedList;

import com.google.common.base.Function;

import fig.basic.LispTree;

public class LimitFormula extends Formula {

  public final Formula number;
  public final Formula set;
  
  public LimitFormula(Formula number, Formula set) {
    this.number = number;
    this.set = set;
  }
  
  @Override
  public List<Formula>getChildren(){
	 
	  LinkedList children = new LinkedList();
	  children.add(this.number);
	  children.add(this.set);
	  return children;
	  
  }
  
  @Override
  public LispTree toLispTree() {
    LispTree tree = LispTree.proto.newList();
    tree.addChild("limit");
    tree.addChild(number.toLispTree());
    tree.addChild(set.toLispTree());
    return tree;
  }

  @Override
  public void forEach(Function<Formula, Boolean> func) {
    throw new RuntimeException("Not yet implemented");

  }

  @Override
  public Formula map(Function<Formula, Formula> func) {
    Formula result = func.apply(this);
    return result == null ? new LimitFormula(number, set.map(func)) : result;
  }

  @Override
  public List<Formula> mapToList(Function<Formula, List<Formula>> func, boolean alwaysRecurse) {
    // TODO Auto-generated method stub
    throw new RuntimeException("Not yet implemented");
  }

  @Override
  public boolean equals(Object o) {
    // TODO Auto-generated method stub
    throw new RuntimeException("Not yet implemented");
  }

  @Override
  public int computeHashCode() {
    // TODO Auto-generated method stub
    throw new RuntimeException("Not yet implemented");
  }

}
