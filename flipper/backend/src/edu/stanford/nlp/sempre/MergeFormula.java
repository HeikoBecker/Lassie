package edu.stanford.nlp.sempre;

import com.google.common.base.Function;
import fig.basic.LispTree;

import java.util.List;
import java.util.LinkedList;

/**
 * Takes two unary formulas and performs either the intersection or union.
 *
 * @author Percy Liang
 */
public class MergeFormula extends Formula {
  public enum Mode { and, or };
  public final Mode mode;
  public final Formula child1;
  public final Formula child2;

  public MergeFormula(Mode mode, Formula child1, Formula child2) {
    this.mode = mode;
    this.child1 = child1;
    this.child2 = child2;
  }

  public LispTree toLispTree() {
    LispTree tree = LispTree.proto.newList();
    tree.addChild(mode.toString());
    tree.addChild(child1.toLispTree());
    tree.addChild(child2.toLispTree());
    return tree;
  }

  @Override
  public void forEach(Function<Formula, Boolean> func) {
    if (!func.apply(this)) { child1.forEach(func); child2.forEach(func); }
  }
  
  @Override
  public String prettyString(){
	  String s;
	  String modeString = "";
	  if (mode.equals(Mode.and)){
		  modeString = "and";
	  }
	  else if (mode.equals(Mode.or)){
		  modeString = "or";
	  }
	  s = this.child1.prettyString() + " "+ modeString + " "+ this.child2.prettyString();
	  if (precisePrettyPrinting){
		  s = "{"+s+"}";
	  }
	  return s;
  }

  @Override
  public List<Formula>getChildren(){
	  LinkedList children = new LinkedList();
	  children.add(this.child1);
	  children.add(this.child2);
	  return children;
	  
  }
  @Override
  public Formula map(Function<Formula, Formula> func) {
    Formula result = func.apply(this);
    return result == null ? new MergeFormula(mode, child1.map(func), child2.map(func)) : result;
  }

  @Override
  public List<Formula> mapToList(Function<Formula, List<Formula>> func, boolean alwaysRecurse) {
    List<Formula> res = func.apply(this);
    if (res.isEmpty() || alwaysRecurse) {
      res.addAll(child1.mapToList(func, alwaysRecurse));
      res.addAll(child2.mapToList(func, alwaysRecurse));
    }
    return res;
  }

  public static Mode parseMode(String mode) {
    if ("and".equals(mode)) return Mode.and;
    if ("or".equals(mode)) return Mode.or;
    return null;
  }

  @SuppressWarnings({"equalshashcode"})
  @Override
  public boolean equals(Object thatObj) {
    if (!(thatObj instanceof MergeFormula)) return false;
    MergeFormula that = (MergeFormula) thatObj;
    if (this.mode != that.mode) return false;
    if (!this.child1.equals(that.child1)) return false;
    if (!this.child2.equals(that.child2)) return false;
    return true;
  }

  public int computeHashCode() {
    int hash = 0x7ed55d16;
    hash = hash * 0xd3a2646c + mode.toString().hashCode();  // Note: don't call hashCode() on mode directly.
    hash = hash * 0xd3a2646c + child1.hashCode();
    hash = hash * 0xd3a2646c + child2.hashCode();
    return hash;
  }
}
