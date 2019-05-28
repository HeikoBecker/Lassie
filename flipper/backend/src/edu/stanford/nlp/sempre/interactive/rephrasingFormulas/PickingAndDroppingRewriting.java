package edu.stanford.nlp.sempre.interactive.rephrasingFormulas;

import edu.stanford.nlp.sempre.Derivation;
import edu.stanford.nlp.sempre.*;
import edu.stanford.nlp.sempre.Executor;
import edu.stanford.nlp.sempre.interactive.robolurn.RoboWorld;
import edu.stanford.nlp.sempre.interactive.robolurn.Item;
import edu.stanford.nlp.sempre.interactive.DALExecutor;
import edu.stanford.nlp.sempre.ActionFormula;
import java.util.*;
import edu.stanford.nlp.sempre.interactive.InteractiveUtils;
import fig.basic.LogInfo;
import fig.basic.Option;
import edu.stanford.nlp.sempre.Session;
import edu.stanford.nlp.sempre.Json;
import fig.basic.LispTree;
import java.awt.Point;
import java.util.stream.Collectors;
public class PickingAndDroppingRewriting extends EquivalentFormulas {

	public static class Options {
		@Option(gloss = "verbose")
		public int verbose = 0;
	}

	public static Options opts = new Options();

	public List<Formula> equivalentFormulas = new LinkedList<Formula>();

	public List<Formula> getEquivalentFormulas() {
		return equivalentFormulas;
		}
	
	private boolean isEveryActionOfType(String actionType, ArrayList path) {
		for (Object pathObj : path) {
			ArrayList pathElement = (ArrayList)pathObj;
			if (! (pathElement.get(2).equals(actionType))) {
				return false;
			}
		}
		return true;
	}
	
	private Set<List<String>> getRelevantItems(ArrayList path){
		Set<List<String>> relevantItems = new HashSet<List<String>>();
		for(Object pathObj : path) {
			ArrayList pathElement = (ArrayList)pathObj;
			relevantItems.add( Arrays.asList((String)pathElement.get(3), (String)pathElement.get(4) ) );
		}
		return relevantItems;
	}
	
	
	private Set<List<String>> getAllPossibleItems(RoboWorld w){
		Set<List<String>> allPossibleItems = new HashSet<List<String>>();
		for (String color : w.getAllColors()) {
			for (String shape : w.getAllShapes()) {
				allPossibleItems.add(Arrays.asList(color, shape));
			}
		}
		return allPossibleItems;
		
	}
	
	private Formula createActionFormulaBasedOnProperty(Formula limitNumberFormula, Formula classSpecificationFormula, Formula actionTypeFormula) {
		Formula quantifiedFormula = Formulas.createQuantifiedItemFormula(limitNumberFormula, classSpecificationFormula);
		Formula finalFormula = new ActionFormula( ActionFormula.Mode.primitive, Arrays.asList( Formulas.newNameFormula("itemActionHandler"), actionTypeFormula, quantifiedFormula ) );
		return finalFormula;
	}
	
	public boolean compareTwoFormulas(Formula f1, Formula f2, Executor executor, ContextValue context) {
		
		  DALExecutor dalExec = (DALExecutor)executor;
		  RoboWorld w1 = dalExec.worldAfterExecution(f1, context);
		  RoboWorld w2 = dalExec.worldAfterExecution(f2, context);
		  
		  return RoboWorld.compareWorlds(w1,w2);
	  }

	
	public PickingAndDroppingRewriting(Parser parser, Derivation deriv, List<String> headTokens, String executionAnswer, Session session){
		RoboWorld worldBefore = RoboWorld.fromContext(session.context);
		RoboWorld worldAfter = worldBefore.clone();
		
		LispTree answerTree = LispTree.proto.parseFromString(executionAnswer);
		String jsonPath = answerTree.child(1).value;
		Map<String, Object> jsonMapping = Json.readMapHard(jsonPath);
		ArrayList path = (ArrayList)jsonMapping.get("path");
		
		Point robotsPoint = worldBefore.getRobotInfo().point;
		//Set<List<String>> relevantItems = getRelevantItems(path);
		Set<List<String>> relevantItems = getAllPossibleItems(worldBefore);
		Formula limitingItemNumberFormula;
		Formula actionTypeFormula;
		Formula itemClassSpecificationFormula;
		Formula quantifiedItemFormula;
		Formula finalFormula;
		LinkedList<Formula> formulasUnderConsideration = new LinkedList<Formula>();
		
		
		if (isEveryActionOfType("pickitem", path) || isEveryActionOfType("dropitem", path)) {
			if (isEveryActionOfType("pickitem", path)) {
				actionTypeFormula = Formulas.newNameFormula("pick");
			}
			
			else  {
				actionTypeFormula = Formulas.newNameFormula("drop");
			}
			
			for (String quantifier : Arrays.asList("single", "every")) {
				
				// combination with only one item
				limitingItemNumberFormula = Formulas.createLimitItemsFormula(quantifier);
				itemClassSpecificationFormula = Formulas.createPropertyFormula(null);
				
				
				finalFormula = createActionFormulaBasedOnProperty(limitingItemNumberFormula, itemClassSpecificationFormula, actionTypeFormula);
				formulasUnderConsideration.add(finalFormula);
				
				for (List<String> colorShapePair : relevantItems) {
					
					// add candidates referred by item color
					itemClassSpecificationFormula = Formulas.createPropertyFormula(colorShapePair.get(0));
					finalFormula = createActionFormulaBasedOnProperty(limitingItemNumberFormula, itemClassSpecificationFormula, actionTypeFormula);
					formulasUnderConsideration.add(finalFormula);
					
					// add candidates referred by item shape
					itemClassSpecificationFormula = Formulas.createPropertyFormula(colorShapePair.get(1));
					finalFormula = createActionFormulaBasedOnProperty(limitingItemNumberFormula, itemClassSpecificationFormula, actionTypeFormula);
					formulasUnderConsideration.add(finalFormula);
					
					// add candidates referred by both color and shape
					for (String connector : Arrays.asList("and", "or")) {
						itemClassSpecificationFormula = Formulas.createPropertyCombinationFormula(colorShapePair.get(0), colorShapePair.get(1), connector);
						finalFormula = createActionFormulaBasedOnProperty(limitingItemNumberFormula, itemClassSpecificationFormula, actionTypeFormula);
						formulasUnderConsideration.add(finalFormula);
					}
					
				}
				
			}
			
			
			
		}
		equivalentFormulas = formulasUnderConsideration.stream().filter(f -> compareTwoFormulas(f, deriv.getFormula(), parser.executor, session.context))
																							.collect(Collectors.toList());
		if (opts.verbose > 1) {
			LogInfo.logs("candidate formulas: %s", formulasUnderConsideration);
			LogInfo.logs("formulas that survived filter = %s", equivalentFormulas);
		}
		
	}

}
