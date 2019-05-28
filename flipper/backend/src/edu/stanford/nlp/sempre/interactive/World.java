package edu.stanford.nlp.sempre.interactive;

import java.awt.Point;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import fig.basic.LogInfo;

import com.beust.jcommander.internal.Sets;

import edu.stanford.nlp.sempre.ContextValue;
import edu.stanford.nlp.sempre.Unit;
import edu.stanford.nlp.sempre.interactive.robolurn.RoboWorld;

/**
 * @param <B> Represents block type
 */
public abstract class World {
  
  public Set<? extends Block> walls;
  public Set<? extends Block> items;
  public Set<Point> open;
  
  public Optional<Set<Point>> selectedArea;
  public Optional<Point> selectedPoint;

  public abstract ActionInterface getActionInterface();
  
  public static World fromContext(String worldname, ContextValue context) {
    if (worldname.equals("RoboWorld"))
      return RoboWorld.fromContext(context);
    throw new RuntimeException("World does not exist: " + worldname);
  }

  public abstract World clone();
  
  public abstract String toJSON();

//  public abstract Map<String,Method> getActionMap();
  
  public abstract String getJSONResponse();

  public abstract Point getHighCorner();

  public abstract Point getLowCorner();
  
  // Lazy eval for now. If the walls (they don't now) change, this will need to be updated.
  public Set<Point> getOpenPoints() {
    if (this.open != null)
      return (Set<Point>) this.open;
    // TODO : this may not handle a non-enclosed space
    Point lc = this.getLowCorner();
    Point hc = this.getHighCorner();
    boolean[][] points = new boolean[hc.y - lc.y + 1][hc.x - lc.x + 1];
    Point p; 
    for (Iterator<? extends Block> iter = walls.iterator(); iter.hasNext(); ) {
      p = iter.next().point;
      points[p.y - lc.y][p.x - lc.x] = true;
    }
    Set<Point> open = new HashSet<>();
    for (int i = lc.x; i < hc.x; ++i) {
      for (int j = lc.y; j < hc.y; ++j) {
        if (!points[j - lc.y][i - lc.x]) {
          open.add(new Point(i, j));
        }
      }
    }
    this.open = open;
    return open;
  }
  
  public abstract Set<? extends Block> has(String rel, Set<Object> values);

  public abstract Set<Object> get(String rel, Set<Block> subset);

  public abstract Set<? extends Object> universalSet(Class<?> clazz);

  public Set<? extends Object> getSpecialSet(String name) {
    if ("world".equals(name)) {
      return getOpenPoints();
    } else if ("items".equals(name)) {
      return allItems();
    }
    return null;
  }
  
  public Set<? extends Block> allItems() {
    return items;
  }
    
  public Set<Point> getSelectedArea() throws UnsetSelectionException {
    if (!selectedArea.isPresent()) {
      throw new UnsetSelectionException();
    }
    return selectedArea.get();
  }
  
  public Point getSelectedPoint() throws UnsetSelectionException {
    if (!selectedPoint.isPresent()) {
      throw new UnsetSelectionException();
    }
    return selectedPoint.get();
  }
  
  public Point makePoint(int x, int y) {
    return new Point(x, y);
  }
  
  public Set<Point> makeArea() {
    return new HashSet<>();
  }
  
  public Set<Point> getAreaWithCorners(Point p1, Point p2) {
    int xHigh = Math.max(p1.x, p2.x);
    int xLow  = Math.min(p1.x, p2.x);
    int yHigh = Math.max(p1.y, p2.y);
    int yLow  = Math.min(p1.y, p2.y);
    return getOpenPoints().stream()
        .filter(p -> p.x >= xLow && p.x <= xHigh && p.y >= yLow && p.y <= yHigh)
        .collect(Collectors.toSet());
  }
  
  public Set<? extends Object> makeArray(Set<Object> a){
	  
	  return a;
  }
  
  
  public Set<Set<Point>> createAreaListFromArea(Set<Point> a){
	  return new HashSet<>(Arrays.asList(a));
  }
  public Set<Point> combineAreas(Object a1, Point p2){
	  HashSet<Point> returnValue = new HashSet<Point>(); 
	  if (a1 instanceof Point){
		  //LogInfo.logs("a1 was instance of point");
		  returnValue.add((Point)a1);
		  returnValue.add(p2);
	  }
	  else if (a1 instanceof Set){
		  //LogInfo.logs("a1 was set of points");
		  returnValue.add(p2);
		  returnValue.addAll((HashSet<Point>)a1);
		  
	  }
	  else {LogInfo.logs("something else happened");}
	  return returnValue;
  }
  
  public Set<? extends Object> combineCollections(Set<Object> c1, Set<Object> c2) {
    Object c1Elem;
    Object c2Elem;
    if (c1.isEmpty() && c2.isEmpty()) return new HashSet<>();
    if (c1.isEmpty()) {
      c2Elem = c2.iterator().next();
      if (c2Elem instanceof Set) {
    	  return c2;
      }
      else if (c2Elem instanceof Point){
    	  return new HashSet<>(Arrays.asList(c2));
      }
      else throw new RuntimeException("Collection 2 of unknown type");
    }
    if (c2.isEmpty()) {
      c1Elem = c1.iterator().next();
      if (c1Elem instanceof Set) {
    	  return c1;
      }
      else if (c1Elem instanceof Point){
    	  return new HashSet<>(Arrays.asList(c1));
      }
      else throw new RuntimeException("Collection 1 of unknown type");
    }
    c1Elem = c1.iterator().next();
    c2Elem = c2.iterator().next();
    if (c1Elem instanceof Set && c2Elem instanceof Set) {
      c1.addAll(c2);
      return c1;
    } else if (c1Elem instanceof Set) {
      c1.add(c2);
      return c1;
    } else if (c2Elem instanceof Set) {
      c2.add(c1);
      return c2;
    } else { // If c1 and c2 are both sets of points
      Set<Set<Object>> set = new HashSet<>();
      set.add(c1);
      set.add(c2);
      return set;
    }
  }
  
  public Point anyPoint(Set<Point> s) {
    if (s.isEmpty())
      return new Point(Integer.MIN_VALUE, Integer.MIN_VALUE);
    ArrayList<Point> arr = new ArrayList<>();
    for (Point p : s)
      arr.add(p);
    return arr.get((int) (System.currentTimeMillis() % arr.size()));
  }
  
  /* returns a randomly chosen area from collection (set of areas)*/
  public Set<Point> anyArea(Set<Set<Point>> collection){
	  if (collection.isEmpty()) {
		  return new HashSet<Point>();
	  }
	  ArrayList<Set<Point>> arr = new ArrayList<>();
	  for (Set<Point> area : collection)
		  arr.add(area);
	  return arr.get((int) (System.currentTimeMillis() % arr.size()));
  }
  
  public World() {
    this.walls = new HashSet<>();
    this.items = new HashSet<>();
  }
}
