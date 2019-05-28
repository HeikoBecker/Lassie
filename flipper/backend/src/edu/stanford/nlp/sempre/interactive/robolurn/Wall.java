package edu.stanford.nlp.sempre.interactive.robolurn;

import java.awt.Point;
import java.util.List;

import org.testng.collections.Lists;

public class Wall extends RoboBlock {

  public static Wall fromJSONObject(List<Object> props) {
    Wall w = new Wall(new Point((Integer) props.get(0), (Integer) props.get(1)));
    return w;
  }

  public Wall(Point point) {
    this.point = point;
  }
  
  @Override
  public Object get(String property) {
    Object propval;
    if (property.equals("point"))
      propval = this.point;
    else
      throw new RuntimeException("getting property " + property + " is not supported.");
    return propval;
  }

  public Object toJSON() {
    List<Object> cube = Lists.newArrayList(point.x, point.y, RoboBlock.WALL_TYPE);
    return cube;
  }

  @Override
  public Wall clone() {
    return  new Wall(new Point(point.x, point.y));
  }

  @Override
  public int hashCode() {
    final int prime = 19;
    int result = 1;
    result = prime * result + point.x;
    result = prime * result + point.y;

    return result;
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj)
      return true;
    if (obj == null)
      return false;
    if (getClass() != obj.getClass())
      return false;
    RoboBlock other = (RoboBlock) obj;

    if (!point.equals(other.point))
      return false;

    return true;
  }

  @Override
  public String toString() {
    return this.toJSON().toString();
  }
}
