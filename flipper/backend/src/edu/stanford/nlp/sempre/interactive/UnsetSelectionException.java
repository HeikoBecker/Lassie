package edu.stanford.nlp.sempre.interactive;

/**
 * Throw this exception when a variable is accessed without it first being set.
 * @author brendonboldt
 *
 */
@SuppressWarnings("serial")
public class UnsetSelectionException extends Exception {

  public static enum Type {
    AREA, POINT;
  }
  
  private Type type;
  
  public UnsetSelectionException(Type type) {
    this.type = type;
  }

  public UnsetSelectionException() {
    
  }
  
  public Type getType() {
    return type;
  }
}
