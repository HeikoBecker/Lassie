package edu.stanford.nlp.sempre;

import fig.basic.LispTree;
import fig.basic.LogInfo;

/**
 * A ValueFormula represents an atomic value which is cannot be decomposed
 * into further symbols.  Simply a wrapper around Value.
 *
 * @author Percy Liang
 */
public class ValueFormula<T extends Value> extends PrimitiveFormula {
  public final T value;

  public ValueFormula(T value) { this.value = value; }
  public LispTree toLispTree() {
    if (value instanceof NameValue) return LispTree.proto.newLeaf(((NameValue) value).id);
    return value.toLispTree();
  }

  @Override
  public String prettyString(){
	  //LogInfo.logs("value is %s of class %s and its sortString is %s", this.value, this.value.getClass(), this.value.sortString());
	  if (value.sortString().equals("items?property")){
		  return "is";
	  }
	  else if (value.sortString().equals("triangle") || value.sortString().equals("circle") || value.sortString().equals("square")){
		  return this.value.contentString();
	  }
	  else if (value.sortString().equals("red") || value.sortString().equals("blue") || value.sortString().equals("green") || value.sortString().equals("yellow")){
		  return this.value.contentString();
	  }
	  else if (value.sortString().equals("all_rooms")){
		  return "rooms";
	  }
	  else
	  {
		  return this.value.contentString();
	  }
  }
  
  @SuppressWarnings({"equalshashcode"})
  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (o == null || getClass() != o.getClass()) return false;
    ValueFormula<?> that = (ValueFormula<?>) o;
    if (!value.equals(that.value)) return false;
    return true;
  }

  public int computeHashCode() {
    return value.hashCode();
  }
}
