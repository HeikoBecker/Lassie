package edu.stanford.nlp.sempre.interactive.rephrasingFormulas;
import edu.stanford.nlp.sempre.Derivation;
import java.util.List;
import edu.stanford.nlp.sempre.Formula;



public abstract class EquivalentFormulas{
	public Formula originalFormula;
	public abstract List<Formula> getEquivalentFormulas(); 
}