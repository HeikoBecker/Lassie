package edu.stanford.nlp.sempre.interactive.robolurn;

import java.awt.Point;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.Objects;
import fig.basic.LogInfo;

import org.testng.collections.Lists;

public class Item extends RoboBlock {

  public final String color;
  public final String shape;
  private boolean carried;
  
  public static Item fromJSONObject(List<Object> props) {
    Item i = new Item(
        new Point((Integer) props.get(0), (Integer) props.get(1)),
        props.get(3).toString(), props.get(4).toString(),
        false
    );
    return i;
  }
  
  public Item(Point point, String color, String shape, boolean carried) {
    if (point == null)
      this.point = new Point(0, 0);
    else
      this.point = point;
    this.color = color;
    this.shape = shape;
    this.carried = carried;
  }
  
  
  public boolean equalCharacteristics(Item otherItem) {
	  return this.color.equals(otherItem.color) && this.shape.equals(otherItem.shape) && this.carried == otherItem.carried && 
			  this.point.x == otherItem.point.x && this.point.y == otherItem.point.y;
  }
  
  @Override
  public int hashCode(){
	  return Objects.hash(point, color, shape, carried);
  }
  
  @Override
  public Object get(String property) {
    Object propval;
    if (property.equals("color")) {
      propval = this.color.toString();
    }
    else if (property.equals("shape"))
        propval = this.shape.toString();
    else if (property.equals("carried"))
      propval = this.carried;
    else if (property.equals("point"))
      propval = this.point;
    else
      throw new RuntimeException("getting property " + property + " is not supported.");
    return propval;
  }

  public Object toJSON() {
    List<Object> cube = Lists.newArrayList(point.x, point.y, color, shape, carried);
    return cube;
  }

  public boolean isCarried() {
    return carried;
  }
  
  public void setCarried(boolean state) {
    if (state == false)
      point = new Point(Integer.MIN_VALUE, Integer.MIN_VALUE);
    carried = state;
  }
  
  
  public String getSpec() {
	  String itemSpec = "{color: "+this.color+", shape: "+this.shape+"}";
	  return itemSpec;
	  
  }
  public boolean isIn(Set<Item> s) {
    Item item;
    for (Iterator<Item> iter = s.iterator(); iter.hasNext(); ) {
      item = iter.next();
      if (item.point.equals(this.point)
          && item.color == this.color && item.shape == this.shape)
        return true;
    }
    return false;
  }
  
  @Override
  public Item clone() {
    return new Item(new Point(point.x, point.y), color, shape, carried);
  }

  @Override
  public String toString() {
    return this.toJSON().toString();
  }
}
