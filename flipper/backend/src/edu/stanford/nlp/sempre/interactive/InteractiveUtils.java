package edu.stanford.nlp.sempre.interactive;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

import org.testng.collections.Lists;

import com.google.common.collect.ImmutableList;

import edu.stanford.nlp.sempre.ActionFormula;
import edu.stanford.nlp.sempre.BeamParser;
import edu.stanford.nlp.sempre.Derivation;
import edu.stanford.nlp.sempre.Example;
import edu.stanford.nlp.sempre.Formula;
import edu.stanford.nlp.sempre.Formulas;
import edu.stanford.nlp.sempre.IdentityFn;
import edu.stanford.nlp.sempre.Json;
import edu.stanford.nlp.sempre.Master;
import edu.stanford.nlp.sempre.Params;
import edu.stanford.nlp.sempre.Parser;
import edu.stanford.nlp.sempre.Rule;
import edu.stanford.nlp.sempre.SemanticFn;
import edu.stanford.nlp.sempre.Session;
import fig.basic.LispTree;
import fig.basic.LogInfo;
import fig.basic.Option;
import fig.basic.Ref;

/**
 * Utilities for interactive learning
 *
 * @author sidaw
 */


public final class InteractiveUtils {
  public static class Options {
    @Option(gloss = "use the best formula when no match or not provided")
    public boolean useBestFormula = false;

    @Option(gloss = "path to the citations")
    public String citationPath;

    @Option(gloss = "verbose")
    public int verbose = 0;
  }

  public static Options opts = new Options();

  private InteractiveUtils() {
  }

  // dont spam my log when reading things in the beginning...
  public static boolean fakeLog = false;

  public static Derivation stripDerivation(Derivation deriv) {
    while (deriv.rule.sem instanceof IdentityFn) {
      deriv = deriv.child(0);
    }
    return deriv;
  }
  
  public static Example exampleFromUtterance(String utt, Session session) {
    Example.Builder b = new Example.Builder();
    b.setId(session.id);
    b.setUtterance(utt);
    b.setContext(session.context);
    Example ex = b.createExample();
    ex.preprocess();
    return ex;
  }

  public static Derivation stripBlock(Derivation deriv) {
    if (opts.verbose > 0)
      LogInfo.logs("StripBlock %s %s %s", deriv, deriv.rule, deriv.cat);
    while ((deriv.rule.sem instanceof BlockFn || deriv.rule.sem instanceof IdentityFn) && deriv.children.size() == 1) {
      deriv = deriv.child(0);
    }
    return deriv;
  }

  public static Derivation derivFromUtteranceAndFormula(String utterance, Formula formula, Parser parser, Params params, Session session){

	  Derivation foundDerivation = null;
	  List<Derivation> allDerivs = new ArrayList<>();
	  Formula targetFormula = formula;
	  
	  String utt = utterance;
	  	  
	  Example exHead = InteractiveUtils.exampleFromUtterance(utt, session);
	  
	  if (exHead.getTokens() == null || exHead.getTokens().size() == 0)
	      throw BadInteractionException.headIsEmpty(utt);
	    
	  InteractiveBeamParserState state = ((InteractiveBeamParser)parser).parseWithoutExecuting(params, exHead, false);
	  
	  
	  
	
	  boolean found = false;
	  for (Derivation d : exHead.predDerivations) {
		if (opts.verbose > 2){
		  LogInfo.logs("Deriv from utteranceAnd formula, predDerivations. considering: %s", d.formula.toString());
		}
		if (d.formula.equals(targetFormula)) {
		  found = true;
		  foundDerivation = stripDerivation(d);
		  break;
		}
	  }
	  if (!found && !formula.equals("?")) {
		  LogInfo.errors("matching formula not found: %s :: %s", utt, formula);
	  }
	  // just making testing easier, use top derivation when we formula is not
	  // given
	  if (!found && exHead.predDerivations.size() > 0 && (formula.equals("?") || formula == null || opts.useBestFormula))
		  foundDerivation = stripDerivation(exHead.predDerivations.get(0));
	  else if (!found) {
		  Derivation res = new Derivation.Builder().formula(targetFormula)
	        // setting start to -1 is important,
	// which grammarInducer interprets to mean we do not want partial
	// rules
				  .withCallable(new SemanticFn.CallInfo("$Action", -1, -1, null, new ArrayList<>())).createDerivation();
	    foundDerivation = res;
	  }
		    
	  if (foundDerivation != null && opts.verbose > 1){
		  LogInfo.logs("derivFromUtteranceAndFormula: returning deriv  %s", foundDerivation);
	  }
	 return foundDerivation;
	
		  
}
	  
  public static List<Derivation> derivsfromJson(String jsonDef, Parser parser, Params params,
      Ref<Master.Response> refResponse, Session session) {
    @SuppressWarnings("unchecked")
    List<Object> body = Json.readValueHard(jsonDef, List.class);
    // string together the body definition
    List<Derivation> allDerivs = new ArrayList<>();
    int numFailed = 0;
    for (Object obj : body) {
      @SuppressWarnings("unchecked")
      List<String> pair = (List<String>) obj;
      String utt = pair.get(0);
      String formula = pair.get(1);
      

      if (formula.equals("()")) {
        LogInfo.logs("Error: Got empty formula");
        continue;
      }
      Formula targetFormula = Formulas.fromLispTree(LispTree.proto.parseFromString(formula));
      Derivation newDerivation = derivFromUtteranceAndFormula(utt, targetFormula, parser, params, session);
      if (newDerivation != null){
    	  allDerivs.add(newDerivation);
      }
     }
     
   
   return allDerivs;
  }

  public static List<String> utterancefromJson(String jsonDef, boolean tokenize) {
    @SuppressWarnings("unchecked")
    List<Object> body = Json.readValueHard(jsonDef, List.class);
    // string together the body definition
    List<String> utts = new ArrayList<>();
    for (int i = 0; i < body.size(); i++) {
      Object obj = body.get(i);
      @SuppressWarnings("unchecked")
      List<String> pair = (List<String>) obj;
      String utt = pair.get(0);

      Example.Builder b = new Example.Builder();
      // b.setId("session:" + sessionId);
      b.setUtterance(utt);
      Example ex = b.createExample();
      ex.preprocess();

      if (tokenize) {
        utts.addAll(ex.getTokens());
        if (i != body.size() - 1 && !utts.get(utts.size() - 1).equals(";"))
          utts.add(";");
      } else {
        utts.add(String.join(" ", ex.getTokens()));
      }

    }
    return utts;
  }

  public static synchronized void addRuleInteractive(Rule rule, Parser parser) {
    if (parser instanceof InteractiveBeamParser) {
      parser.addRule(rule);
    } else {
      throw new RuntimeException("interactively adding rule not supported for parser " + parser.getClass().toString());
    }
  }
  
  /**
   * Deletes a rule interactively from the parser
   * @param rule to be deleted
   * @param parser from where to delete it
   */
  public static synchronized void removeRuleInteractive(Rule rule, Parser parser) {
	    if (parser instanceof InteractiveBeamParser) {
	      parser.removeRule(rule);
	    } else {
	      throw new RuntimeException("interactively removing rule not supported for parser " + parser.getClass().toString());
	    }
	  }

  static Rule blockRule(ActionFormula.Mode mode) {
    BlockFn b = new BlockFn(mode);
    b.init(LispTree.proto.parseFromString("(BlockFn sequential)"));
    return new Rule("$Action", Lists.newArrayList("$Action", "$Action"), b);
  }

  public static Derivation combine(List<Derivation> children) {
    ActionFormula.Mode mode = ActionFormula.Mode.sequential;
    if (children.size() == 1) {
      return children.get(0);
    }
    Formula f = new ActionFormula(mode, children.stream().map(d -> d.formula).collect(Collectors.toList()));
    Derivation res = new Derivation.Builder().formula(f)
        // setting start to -1 is important,
        // which grammarInducer interprets to mean we do not want partial rules
        .withCallable(new SemanticFn.CallInfo("$Action", -1, -1, blockRule(mode), ImmutableList.copyOf(children)))
        .createDerivation();
    return res;
  }

  public static String getParseStatus(Example ex) {
    return GrammarInducer.getParseStatus(ex).toString();
  }
  
  public static enum AuthorDescription{
	  Self, Other, None;
  }
  
  public static boolean otherAuthors(Derivation d, String id) {
	  
	  if (d.rule.source != null && d.rule.source.uid != id) {
		  
		  return true;
	  }
	  else {
		  for (Derivation child : d.children) {
			  if (otherAuthors(child, id) == true) {
				  return true;
			  }
		  }
		  return false;
	  }
	  
  }
  
  // if there is at least one other author involved in the derivations, it is counted as "using other author's definitions"
  // if it is a core-language command, then the author is None. If it is induced, but only one author (the one who sent a command), then it is Self
  public static AuthorDescription getAuthorDescription(Example ex){
	  
	  for (Derivation d : ex.getPredDerivations()) {
		 if (d.isInduced() == false) {
			 return AuthorDescription.None;
		 }
		 else if (otherAuthors(d, ex.id)) {
			  return AuthorDescription.Other;
		 }
		 else {
			  return AuthorDescription.Self;
		  }
	  }
	  return AuthorDescription.None;
  }

  public static void cite(Derivation match, Example ex) {
    CitationTracker tracker = new CitationTracker(ex.id, ex);
    tracker.citeAll(match);
  }
}
