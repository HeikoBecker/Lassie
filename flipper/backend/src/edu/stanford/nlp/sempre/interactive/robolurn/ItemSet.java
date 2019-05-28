package edu.stanford.nlp.sempre.interactive.robolurn;

import java.awt.Point;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Defines a set of items which can have filters specified without the filters
 * being immediately evaluated. This is important in situations where filters
 * need to be evaluated in a different order than they are specified
 */
@SuppressWarnings({ "serial" })
public class ItemSet extends HashSet<Item> {

  public Optional<Boolean> isCarried;
  public Optional<Set<Point>> locFilter;
  public Optional<Integer> limit;
  
  public ItemSet(Set<Item> set) {
    super();
    this.addAll(set);
    isCarried = Optional.empty();
    locFilter = Optional.empty();
    limit = Optional.empty();
  }
  
  public Set<Item> eval() {
    List<Item> list =  this.stream()
        .filter(i -> isCarried.isPresent() ? i.isCarried() == isCarried.get() : true)
        .filter(i -> locFilter.isPresent() ? locFilter.get().contains(i.point) : true)
        .collect(Collectors.toList());
    if (limit.isPresent())
      list = list.subList(0, Math.min(limit.get(), list.size()));
    return new HashSet<>(list);
  }


}
