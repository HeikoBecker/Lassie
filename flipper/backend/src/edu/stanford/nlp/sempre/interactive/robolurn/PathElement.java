package edu.stanford.nlp.sempre.interactive.robolurn;

import java.awt.Point;
import java.util.List;

import org.testng.collections.Lists;

import edu.stanford.nlp.sempre.Json;
import edu.stanford.nlp.sempre.interactive.AbstractPathElement;

public class PathElement extends AbstractPathElement<PathElement.Action> {

  // PATH represents a movement to an adjacent point
  public enum Action {
    PICKITEM, DROPITEM, PATH, DESTINATION;

    public static Action fromString(String s) {
      if (s.toLowerCase().equals("path"))
        return PATH;
      else if (s.toLowerCase().equals("pickitem"))
        return PICKITEM;
      else if (s.toLowerCase().equals("dropitem"))
        return DROPITEM;
      else if (s.toLowerCase().equals("destination"))
        return DESTINATION;
      else
        return PATH;
    }

    @Override
    public String toString() {
      switch(this) {
        case PATH:        return "\"path\"";
        case PICKITEM:    return "\"pickitem\"";
        case DROPITEM:    return "\"dropitem\"";
        case DESTINATION: return "\"destination\"";
        default:          return "\"ERROR\"";
      }
    }
  }
  
  public String color;
  public String shape;

  public PathElement(Point point, Action action, String color, String shape, boolean possible) {
    this(point, action);
    this.color = color;
    this.shape = shape;
    this.possible = possible;
  }

  public PathElement(Point point, Action action) {
    this();
    this.point = point;
    this.action = action;
    this.possible = true;
  }

  public PathElement() { }


  @Override
  public Object get(String property) {
    Object propval;
    if (property.equals("field"))
      propval = this.point;
    else if (property.equals("action"))
      propval = this.action;
    else if (property.equals("color"))
      propval = this.color;
    else if (property.equals("shape"))
        propval = this.shape;
    else if (property.equals("possible"))
      propval = this.possible;
    else
      throw new RuntimeException("getting property " + property + " is not supported.");
    return propval;
  }

  @SuppressWarnings("unchecked")
  public static PathElement fromJSON(String json) {
    List<Object> props = Json.readValueHard(json, List.class);
    return fromJSONObject(props);
  }

  public static PathElement fromJSONObject(List<Object> props) {
    PathElement act = new PathElement();
    act.point = new Point((Integer) props.get(0), (Integer) props.get(1));
    act.action = Action.fromString(((String) props.get(2)));
    if (props.get(3) == null)
      act.color = null;
    else
      act.color = props.get(3).toString();
    if (props.get(4) == null)
        act.shape = null;
      else
        act.shape = props.get(4).toString();
    return act;
  }

  @Override
  public Object toJSON() {	
    @SuppressWarnings("unchecked")
    List<? extends Object> cube =
        Lists.newArrayList(point.x, point.y, action.toString(), "\""+color+"\"", "\""+shape+"\"", possible);
    return cube;
  }

  @Override
  public PathElement clone() {
    PathElement c = new PathElement(new Point(point.x, point.y), this.action, this.color, this.shape, this.possible);
    return c;
  }

  @Override
  public String toString() {
    return this.toJSON().toString();
  }

}
