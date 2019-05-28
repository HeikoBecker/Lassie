package edu.stanford.nlp.sempre.interactive.robolurn;

import java.awt.Point;
import java.util.HashSet;
import java.util.Set;

import edu.stanford.nlp.sempre.ActionFormula;
import edu.stanford.nlp.sempre.NameValue;
import edu.stanford.nlp.sempre.Value;
import edu.stanford.nlp.sempre.ValueFormula;
import edu.stanford.nlp.sempre.interactive.ActionInterface;
import edu.stanford.nlp.sempre.interactive.World;
import fig.basic.LogInfo;

/**
 * Singleton class containing actions which can be performed on RoboWorld
 * @author brendonboldt
 * @author ivan
 *
 */
public class ActionMethods extends ActionInterface {
  
  private static ActionMethods instance = new ActionMethods();
  
  private ActionMethods() { }
  
  public static ActionMethods getInstance() {
    return instance;
  }

  /**
   * Move relative to the current position of the robot 
   */
  public boolean move(RoboWorld world, String dir) {
    Point p = new Point(world.robot.point.x, world.robot.point.y);
    if ("up".equals(dir))
      p.y += 1;
    else if ("down".equals(dir))
      p.y -= 1;
    else if ("right".equals(dir))
      p.x += 1;
    else if ("left".equals(dir))
      p.x -= 1;
    else
      throw new RuntimeException("Unknown direction " + dir);
    return world.gotoPoint(p, new HashSet<>());
  }
  
  /**
   * All action methods return whether the action was successfully completed or not
   */
  public boolean visit(RoboWorld world, Point p, Set<Point> avoidSet) {
    return world.gotoPoint(p, avoidSet);
  }
  
  
  public boolean visit(RoboWorld world, Point p) {
    return world.gotoPoint(p, new HashSet<>());
  }
  
  public boolean visitArea(RoboWorld world, Set<Point> goalSet, Set<Point> avoidSet) {
	    return world.gotoSetOfPoints(goalSet, avoidSet);
	  }
  
  public boolean visitArea(RoboWorld world, Set<Point> goalSet) {
	    return world.gotoSetOfPoints(goalSet, new HashSet<>());
	  }

  
  public boolean visitAreaCollections(RoboWorld world, Set<Set<Point>> setOfAreas, Set<Point> avoidSet){
	  return world.gotoSetOfAreas(setOfAreas, avoidSet);
  }
  
  public boolean visitAreaCollections(RoboWorld world, Set<Set<Point>> setOfAreas){
	  return world.gotoSetOfAreas(setOfAreas, new HashSet<>());
  }
  
  public boolean itemActionHandler(RoboWorld world, String act, ItemSet is) {
    return world.itemActions.get(act).apply(is);
  }

  public boolean noop() {
    return true;
  }
  
  @SuppressWarnings("rawtypes")
  private static String parseFormula(ActionFormula f) {
    Value method = ((ValueFormula) f.args.get(0)).value;
    String id = ((NameValue) method).id;
    switch (id) {
      case "move": 
        //return String.format("move %s", f.args.get(1));
        return "move";
      case "visit": 
        // This code below would provice more information on the nature of the
        // action that failed (currently unfinished).
        //CallFormula cf = (CallFormula) f.args.get(1);
        //int arg1 = (int) ((NumberValue) ((ValueFormula) cf.args.get(0)).value).value;
        //int arg2 = (int) ((NumberValue) ((ValueFormula) cf.args.get(1)).value).value;
        //return String.format("visit [%d,%d]", arg1, arg2);
        return "visit";
      case "itemActionHandler":
        String value = ((NameValue) ((ValueFormula) f.args.get(1)).value).id;
        return value;
      default:
        return f.toString();
    }
  }

  public void handleActionResult(World world, ActionFormula formula, Object resultObj) {
    RoboWorld roboWorld = (RoboWorld) world;
    boolean result = (boolean) resultObj;
    if (!result) {
      // TODO : need more information here
      roboWorld.unrealizableStatus =
          //String.format("Could not complete the action: %s", ActionMethods.parseFormula(formula));
    		  String.format("Could not complete the action: %s", formula.prettyString());
    }
  }
  
}
