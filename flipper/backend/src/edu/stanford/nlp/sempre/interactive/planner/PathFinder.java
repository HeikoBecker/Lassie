package edu.stanford.nlp.sempre.interactive.planner;

import java.awt.Point;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;
import java.util.List;
import java.util.LinkedList;
import java.util.stream.Collectors;
import fig.basic.LogInfo;

import es.usc.citius.hipster.algorithm.Algorithm.SearchResult;
import es.usc.citius.hipster.algorithm.Hipster;
import es.usc.citius.hipster.model.Transition;
import es.usc.citius.hipster.model.function.CostFunction;
import es.usc.citius.hipster.model.function.impl.StateTransitionFunction;
import es.usc.citius.hipster.model.problem.ProblemBuilder;
import es.usc.citius.hipster.model.problem.SearchProblem;
import es.usc.citius.hipster.util.examples.maze.Maze2D;
import faisal22.Christofides;

public class PathFinder {

  /**
   * Finds a path from start to goalSet given a set of wall coordinates.
   * low/highCorner give size of the map.
   */
  public static List<Point> findPath(Iterable<? extends Point> map, Point start, Set<Point> goalSet, Point lowCorner,
      Point highCorner) {
    int xSize = highCorner.x - lowCorner.x + 1;
    int ySize = highCorner.y - lowCorner.y + 1;
    start.x -= lowCorner.x;
    start.y -= lowCorner.y;

    goalSet = goalSet.stream().filter(g -> (g.x >=0 && g.y >= 0 && g.x < xSize && g.y < ySize))
    		.map(g -> new Point(g.x - lowCorner.x, g.y - lowCorner.y)).collect(Collectors.toSet());;

    char[][] charMap = new char[ySize][xSize];

    for (Point p : map) {
      charMap[p.y - lowCorner.y][p.x - lowCorner.x] = Maze2D.Symbol.OCCUPIED.value();
    }
    for (int i = 0; i < ySize; i++) {
      for (int j = 0; j < xSize; j++) {
        if (charMap[i][j] == '\u0000') {
          charMap[i][j] = Maze2D.Symbol.EMPTY.value();
        }
      }
    }
    charMap[start.y][start.x] = Maze2D.Symbol.START.value();
    boolean replaceGoal = false;

    for (Point goal : goalSet){
    	if (charMap[goal.y][goal.x] != Maze2D.Symbol.OCCUPIED.value())
    	charMap[goal.y][goal.x] = Maze2D.Symbol.GOAL.value();
    }
    Maze2D maze = new Maze2D(charMap);
     //LogInfo.logs(maze.toString());


    @SuppressWarnings("rawtypes")
    SearchProblem problem = ProblemBuilder.create().initialState(start).defineProblemWithExplicitActions()
        .useTransitionFunction(new StateTransitionFunction<Point>() {
          @Override
          public Iterable<Point> successorsOf(Point state) {
            // /return maze.validLocationsFrom(state);
            Collection<Point> validMoves = new HashSet<Point>();
            // Check for all valid movements
            try {
              if (maze.isFree(new Point(state.x + 1, state.y)))
                validMoves.add(new Point(state.x + 1, state.y));
              if (maze.isFree(new Point(state.x - 1, state.y)))
                validMoves.add(new Point(state.x - 1, state.y));
              if (maze.isFree(new Point(state.x, state.y + 1)))
                validMoves.add(new Point(state.x, state.y + 1));
              if (maze.isFree(new Point(state.x, state.y - 1)))
                validMoves.add(new Point(state.x, state.y - 1));
            } catch (ArrayIndexOutOfBoundsException ex) {
              // Invalid move!
            }

            return validMoves;
          }
        }).useCostFunction(new CostFunction<Void, Point, Double>() {
          @Override
          public Double evaluate(Transition<Void, Point> transition) {
            Point source = transition.getFromState();
            Point destination = transition.getState();
            return source.distance(destination);
          }
        }).build();
    
    @SuppressWarnings({ "rawtypes", "unchecked" })
    SearchResult result = Hipster.createAStar(problem).search(goalSet);

    // Readjust coordinates
    @SuppressWarnings("unchecked")
    List<Point> path = (List<Point>) result.getOptimalPaths().get(0);
    List<Point> transformed = path.stream().map(p -> {
      p.x += lowCorner.x;
      p.y += lowCorner.y;
      return p;
    }).collect(Collectors.toList());
    return transformed;
  }

  private static double dist(Point p1, Point p2) {
    return Math.sqrt(Math.pow((p1.x - p2.x), 2) + Math.pow((p1.y - p2.y), 2));
  }

  /**
   * Get the order in which to traverse a given set of points
   * This implemented with the Christofides algorithm
   */
  public static int[] getPointOrder(List<Point> points) {
    if (points.size() == 1) {
      return new int[] {0};
    } else if (points.size() == 0) {
      return new int[] {};
    }
    
    double[][] weights = new double[points.size()][points.size()];
    for (int i = 0; i < points.size(); ++i) {
      for (int j = 0; j < points.size(); ++j) {
        if (i == j)
          weights[i][j] = 0.0;
        else
          weights[i][j] = dist(points.get(i), points.get(j));
      }
    }
    Christofides solver = new Christofides(false);
    return solver.solve(weights);
  }
}
