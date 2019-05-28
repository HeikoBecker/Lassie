package edu.stanford.nlp.sempre.interactive;

import edu.stanford.nlp.sempre.ActionFormula;

/**
 * Provides an interface for executing actions on a given world
 * @author brendonboldt
 *
 */
public abstract class ActionInterface {

  public abstract void handleActionResult(World world, ActionFormula actionName, Object result);
  
}
