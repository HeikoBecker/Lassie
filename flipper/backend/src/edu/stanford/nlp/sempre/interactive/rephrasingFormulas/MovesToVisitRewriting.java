package edu.stanford.nlp.sempre.interactive.rephrasingFormulas;

import edu.stanford.nlp.sempre.Derivation;
import edu.stanford.nlp.sempre.*;
import edu.stanford.nlp.sempre.ActionFormula;
import java.util.*;
import edu.stanford.nlp.sempre.interactive.InteractiveUtils;
import fig.basic.LogInfo;
import fig.basic.Option;
import edu.stanford.nlp.sempre.Session;
import edu.stanford.nlp.sempre.Json;
import fig.basic.LispTree;
public class MovesToVisitRewriting extends EquivalentFormulas {

	public static class Options {
		@Option(gloss = "verbose")
		public int verbose = 0;
	}

	public static Options opts = new Options();

	public List<Formula> equivalentFormulas = new LinkedList<Formula>();

	public List<Formula> getEquivalentFormulas() {
		return equivalentFormulas;
		}
	
	private ActionFormula createVisitConstantFieldFormula( int x, int y ) {

		NumberValue xCoord = new NumberValue((double)x);
		NumberValue yCoord = new NumberValue((double) y);
		
		List<Formula> listOfValues = Arrays.asList(new ValueFormula(xCoord), new ValueFormula(yCoord));
		CallFormula createdPoint = new CallFormula("makePoint", listOfValues);
		List<Formula> actionFormulaArgs = Arrays.asList( new ValueFormula(new NameValue("visit", null)), createdPoint );
		ActionFormula visitFormula = new ActionFormula(ActionFormula.Mode.primitive, actionFormulaArgs);		
		return visitFormula;
	}
	
	private boolean isPrimitiveMove(Formula f) {
		if (!( f instanceof ActionFormula)) {
			return false;
		}
		ActionFormula actionF = (ActionFormula) f;
		if (actionF.mode.equals(ActionFormula.Mode.primitive) && actionF.args.get(0).toString().equals("move")) {		
			return true;
		}
		else {
			return false;
		}
	}
	
	
	private boolean isFormulaSequenceOfMoves(Formula f) {
		if (opts.verbose > 0) {
			LogInfo.logs("receives formula %s", f);
		}
				
		
		
		if (!( f instanceof ActionFormula)) {
			return false;
		}
		ActionFormula actionF = (ActionFormula) f;
		
		if (actionF.mode.equals(ActionFormula.Mode.repeat) && isFormulaSequenceOfMoves(actionF.args.get(1))) {
			return true;
		}
		
		// if formula is only one move
		if (isPrimitiveMove(actionF)) {
			return true;
		}

		if (! actionF.mode.equals(ActionFormula.Mode.sequential)) {
			return false;
		}
		// if not just one move, then the first argument should be a sequence, while the second one should be one move
		return isFormulaSequenceOfMoves(actionF.args.get(0)) && isPrimitiveMove(actionF.args.get(1));
	}

	public MovesToVisitRewriting(Derivation deriv, List<String> headTokens, String executionAnswer, Session session){
		if (opts.verbose > 0) {
			LogInfo.logs("sent deriv = %s, headTokens = %s, executionAnswer = %s, context = %s", deriv, headTokens, executionAnswer, session.context);
			LogInfo.logs("formula = %s", deriv.getFormula());
		}
		
		LispTree answerTree = LispTree.proto.parseFromString(executionAnswer);
		String jsonPath = answerTree.child(1).value;
		Map<String, Object> jsonMapping = Json.readMapHard(jsonPath);
		ArrayList path = (ArrayList)jsonMapping.get("path");
		
		if (isFormulaSequenceOfMoves(deriv.getFormula()) == true) {
			Object lastElementObject = path.get(path.size()-1);
			ArrayList lastElement = (ArrayList)lastElementObject;
			int x =  ((Integer)lastElement.get(0)).intValue();
			int y = ((Integer) lastElement.get(1)).intValue();
			ActionFormula visitFormula = createVisitConstantFieldFormula(x, y);
			if (opts.verbose > 0) {
				LogInfo.logs("created formula = %s", visitFormula);
			}
			equivalentFormulas.add(visitFormula);
		}
		
			
			
	}

}
