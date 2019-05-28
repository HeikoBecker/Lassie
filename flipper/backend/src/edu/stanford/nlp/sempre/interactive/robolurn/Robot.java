package edu.stanford.nlp.sempre.interactive.robolurn;

import java.awt.Point;

public class Robot {
  
  public Point point;

  public Robot(Point point) {
    this.point = point;
  }
  
  public String toString(){	  
	  return this.point.toString();
  }
  
  public Robot clone() {
    return new Robot(new Point(point));
  }
}
