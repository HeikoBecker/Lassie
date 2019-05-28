package edu.stanford.nlp.sempre.interactive;

import java.awt.Point;

public abstract class Block {
  
  public Point point;
  
  public abstract String toString();

  public abstract Object get(String property);
  
  public abstract Block clone();
}
