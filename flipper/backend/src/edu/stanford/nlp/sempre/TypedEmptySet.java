package edu.stanford.nlp.sempre;

import java.util.HashSet;
import java.util.Set;

/**
 * An empty set with a known type at runtime.
 * @author brendonboldt
 * This class serves as a placeholder for operations resulting from the
 * complement of the intersection of disjoint sets. It is the job of the methods
 * which receive this to insert the appropriate universal set.
 * Thanks, type erasure.
 */
@SuppressWarnings({ "rawtypes", "serial" })
public class TypedEmptySet extends HashSet {
  
  public final Class<?> type;
  
  public TypedEmptySet(Class<?> type) {
    this.type = type;
  }
  
  public TypedEmptySet(Set<Object> set) {
    if (set instanceof TypedEmptySet)
      type = ((TypedEmptySet) set).type;
    else if (set.isEmpty())
      throw new RuntimeException(
          "Cannot create a typed EmptySet from a set with no elements.");
    else
      type = set.iterator().next().getClass();
  }
  
  public TypedEmptySet(Set<Object> set1, Set<Object> set2) {
    if (set1 instanceof TypedEmptySet)
      type = ((TypedEmptySet) set1).type;
    else if (set2 instanceof TypedEmptySet)
      type = ((TypedEmptySet) set2).type;
    else if (set1.isEmpty() && set2.isEmpty())
      throw new RuntimeException(
          "Cannot create a typed EmptySet from a set with no elements.");
    else if (set1.isEmpty())
      type = set2.iterator().next().getClass();
    else
      type = set1.iterator().next().getClass();
  }

}
