package edu.stanford.nlp.sempre;

import edu.stanford.nlp.sempre.*;
import edu.stanford.nlp.sempre.interactive.DALExecutor;
import edu.stanford.nlp.sempre.interactive.lassie.LassieUtils;

import fig.basic.LispTree;
import fig.basic.LogInfo;
import fig.basic.Option;

import java.util.List;
import java.util.LinkedList;
import java.util.Arrays;

/**
 * Given a set, returns an element of that set. Kills derivations which
 * execute to empty sets. Sets which execute to something bigger than a
 * singleton trigger a warning, written to the socket file, which
 * locates and describes the ambiguity. In the case that SEMPRE returns
 * no derivations, Lassie can use this information to describe the cause
 * of missing derivations. The grammar rule using this SemanticFn might
 * look like
 *
 * (rule $MyType ($MyTypeCandidates) (ChoiceFn))
 *
 * where $MyTypeCandidates is an executable formula (i.e. ActionFormula
 * if using DALExecutor) returning a StringValue. $MyType will be a
 * StringValue as well.
 */

public class ChoiceFn extends SemanticFn {
    public static class Options {
	@Option(gloss = "Verbose") public int verbose = 0;
    }

    public static Options opts = new Options();

    public String[] elements;
    
    public ChoiceFn() { }

    public DerivationStream call(final Example ex, final Callable c) {
	DALExecutor executor = new DALExecutor();
	String candidates = executor.execute(c.child(0).formula, ex.context).value.pureString();
	elements = candidates.split(","); // current representation of sets is as a string (comma-separated)
	if (elements.length > 1) {
	    LassieUtils.printToSocket("Lassie.AMBIGUITY_WARNING := SOME {set= "
				      + "[\""
				      + candidates.replace(",","\",\"")
				      + "\"]"
				      + ", span= (0,0)}"); // TODO: Find span in derivation and put here
	    elements = new String[0];
	}
	return new MultipleDerivationStream() {
	    public int currIndex = 0;
	    @Override
	    public Derivation createDerivation() {
		if (currIndex >= elements.length || elements[0].equals("")) return null;
		else {
		    Derivation res = new Derivation.Builder()
			.withCallable(c)
			.withStringFormulaFrom(elements[currIndex++])
			.createDerivation();
		    return res;
		}
	    }
	};
    }   
}
