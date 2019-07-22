package edu.stanford.nlp.sempre;

import edu.stanford.nlp.sempre.*;
import edu.stanford.nlp.sempre.interactive.DALExecutor;

import fig.basic.LispTree;
import fig.basic.LogInfo;
import fig.basic.Option;

import java.util.List;
import java.util.LinkedList;
import java.util.Arrays;

/**
 * Given a set, returns an element of that set. Kills derivations which
 * execute to empty sets. Branch a derivation to every possible pick in
 * case it executes to something bigger than a singleton. The grammar
 * rule using this SemanticFn might look like
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

    // public ChoiceFn(List<String> l) {
    //     init(LispTree.proto.newList("ChoiceFn", l));
    // }

    // public void init(LispTree tree) {
    // 	super.init(tree);
    // 	this.l = (new ListValue(tree.child(1))).values;
    // }

    public DerivationStream call(final Example ex, final Callable c) {
	DALExecutor executor = new DALExecutor();
	String candidates = executor.execute(c.child(0).formula, ex.context).value.pureString();
	elements = candidates.split(","); // current representation of sets is as a string (CSVs)
	return new MultipleDerivationStream() {
	    public int currIndex = 0;
	    @Override
	    public Derivation createDerivation() {
		if (currIndex >= elements.length) return null;
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
