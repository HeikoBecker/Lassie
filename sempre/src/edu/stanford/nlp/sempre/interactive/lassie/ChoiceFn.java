package edu.stanford.nlp.sempre;

import edu.stanford.nlp.sempre.*;

import fig.basic.LispTree;
import fig.basic.LogInfo;
import fig.basic.Option;

import java.util.List;
import java.util.LinkedList;
import java.util.Arrays;

/**
 * Given a set, returns an element of that set. Currently only defined for singleton sets.
 * Intends to ensure determinism of grammar in cases of ambiguity.
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
	String phrase = c.childStringValue(0);
	elements = phrase.split(",");
	return new SingleDerivationStream() {
	    @Override
	    public Derivation createDerivation() {
		if (elements.length != 1) return null;
		else {
		    Derivation res = new Derivation.Builder()
			.withCallable(c)
			.withStringFormulaFrom(elements[0])
			.createDerivation();
		    return res;
		}
	    }
	};
    }
}
