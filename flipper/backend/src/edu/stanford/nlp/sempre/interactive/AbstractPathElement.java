package edu.stanford.nlp.sempre.interactive;

import java.awt.Point;
import java.util.List;

/**
 * A PathElement is an atomic action for the robot to perform.
 * @author brendonboldt
 * Generic type A represents an action type
 * @param <A>
 */
public abstract class AbstractPathElement<A> {
  
  public A action;
  public Point point;
  public boolean possible;
  
  public abstract Object get(String property);

  public abstract Object toJSON();
  
  public abstract AbstractPathElement<A> clone();
}
