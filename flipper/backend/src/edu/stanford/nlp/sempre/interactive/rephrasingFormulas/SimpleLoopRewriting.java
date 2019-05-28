package edu.stanford.nlp.sempre.interactive.rephrasingFormulas;
import edu.stanford.nlp.sempre.Derivation;
import edu.stanford.nlp.sempre.*;
import edu.stanford.nlp.sempre.ActionFormula;
import java.util.*;
import edu.stanford.nlp.sempre.interactive.InteractiveUtils;
import fig.basic.LogInfo;
import fig.basic.Option;

public class SimpleLoopRewriting extends EquivalentFormulas {
	
	public static class Options {
	    @Option(gloss = "verbose")
	    public int verbose = 0;
	  }

	  public static Options opts = new Options();

	public LinkedList<Formula> equivalentFormulas = new LinkedList<Formula>();
	public List<Formula> getEquivalentFormulas(){
		return equivalentFormulas;
	}
	
	
	private LinkedList<Formula> flattenActionsConstruct(Formula f){
		LinkedList<Formula> actionList = new LinkedList<Formula>();
		
		if ( !(f instanceof ActionFormula) ) {
			return actionList;
		}
		ActionFormula actionF = (ActionFormula) f;
		if ( actionF.mode.equals(ActionFormula.Mode.primitive) ) {
			actionList.add(actionF);
			return actionList;
		}
		
		if (actionF.mode.equals(ActionFormula.Mode.sequential)) {
			for (Formula fChild : actionF.args) {
				actionList.addAll( flattenActionsConstruct(fChild));
			}
			return actionList;
		}
		
		
		
		
		// if there are some other formulas (non-primitive) return empty action list
		return actionList;
		
	}
	
	private Formula repeatedActionFormula(int numberOfRepetitions, Formula formulaToRepeat){
		LinkedList<Formula> formulaArguments = new LinkedList<Formula>();
		ActionFormula.Mode mode = ActionFormula.Mode.repeat;
		formulaArguments.add(new ValueFormula(new NumberValue(numberOfRepetitions)));
		
		if (opts.verbose > 1){
			LogInfo.logs("formulaTo repeat = %s", formulaToRepeat.toString());
		}
		formulaArguments.add(formulaToRepeat);
		Formula formulaToAdd = new ActionFormula(mode, formulaArguments);
		return formulaToAdd;
	}
	  
	public SimpleLoopRewriting(Derivation deriv, List<String> headTokens){
		originalFormula = deriv.getFormula();
		if (opts.verbose > 1){
			LogInfo.logs(deriv.toString());
			deriv.printDerivationRecursively();
			LogInfo.logs("original formula = %s", originalFormula);
			LogInfo.logs("----------");
		}
		
		
		
		//could this be replaced by working directly on the formula of derivation
		LinkedList<Formula> listOfActions = flattenActionsConstruct(deriv.getFormula());
		
		if (opts.verbose > 1) {
			LogInfo.logs("flatten list of action = %s", listOfActions);
		}
		
		LinkedList<Formula> reformulatedListOfActions = new LinkedList<Formula>();
	
		boolean repetitionOccurred = false;
		if (listOfActions.size() > 0){
			Formula currentCandidate = listOfActions.get(0);
			
			int numberOfRepetitions = 0;
			for (Formula f : listOfActions){
				
				
				if (f.equals(currentCandidate)){
					numberOfRepetitions++;
				}
				
				else {
					if (numberOfRepetitions > 1){
						repetitionOccurred = true;
						reformulatedListOfActions.add(repeatedActionFormula(numberOfRepetitions, currentCandidate));
					}
					else{
						reformulatedListOfActions.add(currentCandidate);
					}
					currentCandidate = f;
					numberOfRepetitions = 1;
				}
			}
			
			if (numberOfRepetitions > 1){
				repetitionOccurred = true;
				reformulatedListOfActions.add(repeatedActionFormula(numberOfRepetitions, currentCandidate));
			}			
			else{
				reformulatedListOfActions.add(currentCandidate);
			}
			if (opts.verbose > 1) {
				LogInfo.logs("reformulated list of actions = %s", reformulatedListOfActions);
			}
			
			ActionFormula.Mode modeOfFormula = ActionFormula.Mode.sequential;
			if (opts.verbose > 1){
				LogInfo.logs("EQUIVALENT REWRITING: reformulated list: %s", reformulatedListOfActions.toString());
			}
			if (repetitionOccurred == true) {
				if (reformulatedListOfActions.size() > 1) {
					equivalentFormulas.add(new ActionFormula(modeOfFormula, reformulatedListOfActions));					
				} else if (reformulatedListOfActions.size() == 1) {
					equivalentFormulas.add(reformulatedListOfActions.get(0));
				}
			}
		}
		if (opts.verbose > 0) {
			LogInfo.logs("EQUIVALENT REWRITING: equivalentFormulas = %s", equivalentFormulas);
		}
	}
		
	
}
