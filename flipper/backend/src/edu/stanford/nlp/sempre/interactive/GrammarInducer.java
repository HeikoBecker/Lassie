package edu.stanford.nlp.sempre.interactive;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;
import java.util.Arrays;
import java.util.stream.Collectors;

import com.beust.jcommander.internal.Lists;
import com.google.common.base.Function;

import edu.stanford.nlp.sempre.ActionFormula;
import edu.stanford.nlp.sempre.ConstantFn;
import edu.stanford.nlp.sempre.Derivation;
import edu.stanford.nlp.sempre.Example;
import edu.stanford.nlp.sempre.Executor;
import edu.stanford.nlp.sempre.Formula;
import edu.stanford.nlp.sempre.ValueFormula;
import edu.stanford.nlp.sempre.Formulas;
import edu.stanford.nlp.sempre.IdentityFn;
import edu.stanford.nlp.sempre.LambdaFormula;
import edu.stanford.nlp.sempre.Rule;
import edu.stanford.nlp.sempre.SemanticFn;
import edu.stanford.nlp.sempre.VariableFormula;
import edu.stanford.nlp.sempre.Params;
import edu.stanford.nlp.sempre.Parser;
import edu.stanford.nlp.sempre.Session;
import edu.stanford.nlp.sempre.NameValue;

import fig.basic.LispTree;
import fig.basic.LogInfo;
import fig.basic.Option;
import edu.stanford.nlp.sempre.interactive.embeddings.Embeddings;
import edu.stanford.nlp.sempre.interactive.rephrasingFormulas.SimpleLoopRewriting;
import edu.stanford.nlp.sempre.interactive.rephrasingFormulas.MovesToVisitRewriting;
import edu.stanford.nlp.sempre.interactive.rephrasingFormulas.VisitDestinationRewriting;
import edu.stanford.nlp.sempre.interactive.rephrasingFormulas.PickingAndDroppingRewriting;

/**
 * Takes two examples, and induce Rules
 *
 * @author sidaw
 */

public class GrammarInducer {
	public static class Options {
		@Option(gloss = "categories that can serve as rules")
		public Set<String> filteredCats = new HashSet<String>();
		@Option(gloss = "verbose")
		public int verbose = 0;
		@Option(gloss = "cats that never overlap, and always safe to replace")
		public List<String> simpleCats = Lists.newArrayList("Color", "Number", "Direction");
		@Option(gloss = "cats that should never be the lhs of induced rules")
		public List<String> nonInducingCats = Lists.newArrayList("$TOKEN", "$PHRASE", "$LEMMA_TOKEN", "$LEMMA_PHRASE");
		@Option(gloss = "use best packing")
		public boolean useBestPacking = true;
		@Option(gloss = "use simple packing")
		public boolean useSimplePacking = true;
		@Option(gloss = "maximum nonterminals in a rule")
		public long maxNonterminals = 4;
		@Option(gloss = "whether to use simple loop rewriting when looking for equivalent formulas")
		public boolean useLoopRewriting = false;
		@Option(gloss = "whether to use rewriting of formulas when inducing new grammar rules")
		public boolean useEquivalentRewriting = false;
		@Option(gloss = "whether to use special token category in order to keep track of keywords")
		public boolean useSpecialTokens = false;
		@Option(gloss = "whether to use rewriting of move formulas into single visit formulas")
		public boolean useMovesToVisitRewriting = false;
		@Option(gloss = "whether to use rewriting of destination")
		public boolean useVisitDestinationRewriting = false;
		@Option(gloss = "whether to use rewriting of picking and dropping")
		public boolean usePickingAndDroppingRewriting = false;
		@Option(gloss = "whether to use similarity when deciding which rewriting to use")
		public boolean useSemanticSimilarityOfSentences = false;
		@Option(gloss = "weight to put to semantic similarity of sentences")
		public double wordEmbeddingsWeight = 1.0;
		@Option(gloss = "weight to put to the score of packing (learnt model)")
		public double packingScoreWeight = 1.0;

	}

	public static Options opts = new Options();

	private List<Rule> inducedRules = null;

	List<String> headTokens;
	String id;

	public List<Derivation> matches;

	public GrammarInducer(List<String> headTokens, Derivation def1, List<Derivation> chartListArg) {
		this(headTokens, def1, chartListArg, null, null, null, null);
	}

	public GrammarInducer(List<String> headTokens, Derivation def1, List<Derivation> chartListArg, Parser parser,
			Params params, Session session) {
		this(headTokens, def1, chartListArg, parser, params, session, "");
	}

	public GrammarInducer(List<String> headTokens, Derivation def1, List<Derivation> chartListArg, Parser parser,
			Params params, Session session, String executionAnswer) {
		this(headTokens, def1, chartListArg, parser, params, session, executionAnswer, null);
	}

	private Derivation createInducedDerivationFromFormula(Formula f, Parser parser, Params params, Session session) {
		Derivation equivalentDerivation = InteractiveUtils.derivFromUtteranceAndFormula(f.prettyString(), f, parser,
				params, session);

		if (equivalentDerivation.grammarInfo.start == -1) {
			equivalentDerivation.grammarInfo.start = 0;
			equivalentDerivation.grammarInfo.end = headTokens.size();

		}
		return equivalentDerivation;

	}

	// induce rule if possible,
	// otherwise set the correct status
	public GrammarInducer(List<String> headTokens, Derivation def1, List<Derivation> chartListArg, Parser parser,
			Params params, Session session, String executionAnswer, Embeddings embeddings) {
		// grammarInfo start and end is used to indicate partial, when using aligner
		boolean allHead = false;
		if (def1.grammarInfo.start == -1) {
			def1.grammarInfo.start = 0;
			def1.grammarInfo.end = headTokens.size();
			allHead = true;
		}

		Packing bestScoredPacking;
		List<Derivation> bestPacking;

		// dont want weird cat unary rules with strange semantics
		if (headTokens == null || headTokens.isEmpty()) {
			throw new RuntimeException("The head is empty, refusing to define.");
		}

		if (executionAnswer.equals("") && opts.useMovesToVisitRewriting) {
			throw new RuntimeException("When using rewriting, the execution path must not be empty");
		}
		// take this into account!
		chartListArg.removeIf(d -> d.start == def1.grammarInfo.start && d.end == def1.grammarInfo.end);
		Derivation originalDerivation = def1;

		this.headTokens = headTokens;
		int numTokens = headTokens.size();
		LinkedList<Derivation> equivalentDerivationsToTry = new LinkedList<Derivation>();

		List<Formula> equivalentFormulas;
		if (opts.useEquivalentRewriting == true && parser != null) {
			if (opts.useLoopRewriting) {

				SimpleLoopRewriting rewriting = new SimpleLoopRewriting(originalDerivation, headTokens);

				equivalentFormulas = rewriting.getEquivalentFormulas();
				for (Formula f : equivalentFormulas) {
					Derivation equivalentDerivation = createInducedDerivationFromFormula(f, parser, params, session);
					equivalentDerivationsToTry.add(equivalentDerivation);
					allHead = true;
				}
			}

			if (opts.useMovesToVisitRewriting == true) {
				MovesToVisitRewriting movesRewriting = new MovesToVisitRewriting(originalDerivation, headTokens,
						executionAnswer, session);
				equivalentFormulas = movesRewriting.getEquivalentFormulas();
				for (Formula f : equivalentFormulas) {
					Derivation equivalentDerivation = createInducedDerivationFromFormula(f, parser, params, session);
					equivalentDerivationsToTry.add(equivalentDerivation);
					allHead = true;
				}
			}
			if (opts.useVisitDestinationRewriting == true) {
				VisitDestinationRewriting destinationRewriting = new VisitDestinationRewriting(originalDerivation,
						headTokens, executionAnswer, session);
				equivalentFormulas = destinationRewriting.getEquivalentFormulas();
				for (Formula f : equivalentFormulas) {

					Derivation equivalentDerivation = createInducedDerivationFromFormula(f, parser, params, session);
					equivalentDerivationsToTry.add(equivalentDerivation);
					allHead = true;
				}
			}
			if (opts.usePickingAndDroppingRewriting == true) {
				PickingAndDroppingRewriting PNDRewriting = new PickingAndDroppingRewriting(parser, originalDerivation,
						headTokens, executionAnswer, session);
				equivalentFormulas = PNDRewriting.getEquivalentFormulas();
				for (Formula f : equivalentFormulas) {
					Derivation equivalentDerivation = createInducedDerivationFromFormula(f, parser, params, session);
					equivalentDerivationsToTry.add(equivalentDerivation);
					allHead = true;
				}
			}
		}
		if (opts.verbose > 0) {
			LogInfo.logs("equivalent derivations = %s", equivalentDerivationsToTry);
			LogInfo.logs("candidate formulas are:");
			for (Derivation dEq : equivalentDerivationsToTry) {

				LogInfo.logs("%s", dEq.getFormula().prettyString());
			}
		}

		inducedRules = new ArrayList<>();
		List<Derivation> chartList = chartListArg;
		this.matches = new ArrayList<>();
		addMatches(originalDerivation, makeChartMap(chartList));
		Collections.reverse(this.matches);
		if (allHead && opts.useSimplePacking) {
			List<Derivation> filteredMatches = this.matches.stream().filter(d -> {
				return opts.simpleCats.contains(getCategoryStringFromDerivation(d)) && d.allAnchored()
						&& d.end - d.start == 1;
			}).collect(Collectors.toList());
			if (opts.verbose > 2) {
				LogInfo.logs("filtered matches = %s", filteredMatches.toString());
			}

			List<Derivation> packing = new ArrayList<>();
			for (int i = 0; i <= headTokens.size(); i++) {
				for (Derivation d : filteredMatches) {
					if (d.start == i) {
						packing.add(d);
						break;
					}
				}
			}

			if (opts.verbose > 2) {
				LogInfo.logs("packing = %s", packing.toString());
			}

			HashMap<String, String> formulaToCatSimple;
			formulaToCatSimple = new HashMap<>();
			packing.forEach(d -> formulaToCatSimple.put(catFormulaKey(d), varName(d, originalDerivation)));
			buildFormula(originalDerivation, formulaToCatSimple);

			List<Rule> simpleInduced = induceRules(packing, originalDerivation);
			for (Rule rule : simpleInduced) {
				rule.addInfo("simple_packing", "true");
				filterRule(rule);
			}

			if (opts.verbose > 1) {
				LogInfo.logs("chartList.size = %d", chartList.size());
				LogInfo.log("Potential packings: ");
				this.matches.forEach(d -> LogInfo.logs("%f: %s\t %s", d.getScore(), d.formula, d.allAnchored()));
				LogInfo.logs("packing: %s", packing);
				LogInfo.logs("formulaToCatSimple: %s", formulaToCatSimple);
			}
		}

		if (opts.useBestPacking == true) {
			// first, use best packing on the original definition
			chartList = chartListArg;
			this.matches = new ArrayList<>();
			addMatches(originalDerivation, makeChartMap(chartList));
			Collections.reverse(this.matches);
			bestScoredPacking = bestPackingDP(this.matches, numTokens);
			double originalDerivationPackingScore = bestScoredPacking.score;
			bestPacking = bestScoredPacking.packing;
			HashMap<String, String> formulaToCatOriginalBestPacking = new HashMap<>();

			bestPacking.forEach(
					d -> formulaToCatOriginalBestPacking.put(catFormulaKey(d), varName(d, originalDerivation)));
			buildFormula(originalDerivation, formulaToCatOriginalBestPacking);
			for (Rule rule : induceRules(bestPacking, originalDerivation)) {

				filterRule(rule);
			}
			// then, find the best equivalent packing
			if (opts.useEquivalentRewriting == true) {
				double overallBestPackingScore = -1.0;
				double overallBestSemScore = -1.0;
				List<Derivation> bestScoringEquivalentPacking = null;
				Derivation bestScoringEquivalentDefinition = null;
				for (Derivation def : equivalentDerivationsToTry) {
					chartList = chartListArg;
					if (opts.verbose > 1) {
						LogInfo.logs("Grammar inducer: examining derivation %s", def.toString());
					}
					this.matches = new ArrayList<>();
					addMatches(def, makeChartMap(chartList));
					Collections.reverse(this.matches);
					bestScoredPacking = bestPackingDP(this.matches, numTokens);
					bestPacking = bestScoredPacking.packing;
					if (opts.verbose > 1) {
						LogInfo.logs("best packing score = %f", bestScoredPacking.score);
					}
					double currentSemScore = semanticScore(headTokens, def, embeddings);
					double currentPackingScore = bestScoredPacking.score;
					if (opts.verbose > 1) {
						LogInfo.logs("++ packScore = %f, semScore = %f", currentPackingScore, currentSemScore);
					}

					if (greaterScore(currentSemScore, currentPackingScore, overallBestSemScore,
							overallBestPackingScore)) {
						bestScoringEquivalentPacking = bestPacking;
						bestScoringEquivalentDefinition = def;
						overallBestSemScore = currentSemScore;
						overallBestPackingScore = currentPackingScore;
					}
				}
				if (bestScoringEquivalentDefinition != null) {
					Derivation finalDefinition = bestScoringEquivalentDefinition;
					if (opts.verbose > 0) {
						LogInfo.logs("best scoring equivalent definition = %s", finalDefinition);
					}
					HashMap<String, String> formulaToCatBestEquivalent = new HashMap<>();
					bestScoringEquivalentPacking.forEach(
							d -> formulaToCatBestEquivalent.put(catFormulaKey(d), varName(d, finalDefinition)));
					buildFormula(finalDefinition, formulaToCatBestEquivalent);
					if (opts.verbose > 1) {
						LogInfo.logs("chartList.size = %d", chartList.size());
						LogInfo.log("Potential packings: ");
						this.matches.forEach(d -> LogInfo.logs("%f: %s\t", d.getScore(), d.formula));
						LogInfo.logs("BestPacking: %s", bestScoringEquivalentPacking);
						LogInfo.logs("formulaToCat: %s", formulaToCatBestEquivalent);
					}
					double originalDerivationSemScore = semanticScore(headTokens, originalDerivation, embeddings);
					if (opts.verbose > 0) {
						LogInfo.logs(
								"equivalent derivation sem score= %f, equivalent derivation packing score = %f, original def sem score = %f, original def pack score = %f",
								overallBestSemScore, overallBestPackingScore, originalDerivationSemScore,
								originalDerivationPackingScore);
					}

					// if the best equivalent packing is good enough (better score than original
					// packing), induce it, too
					if (greaterScore(overallBestSemScore, overallBestPackingScore, originalDerivationSemScore,
							originalDerivationPackingScore)) {
						for (Rule rule : induceRules(bestScoringEquivalentPacking, finalDefinition)) {
							// ALTER : I am not sure why this is here, but it prevents some use cases from
							// being defined
							// if (rule.rhs.stream().allMatch(s -> Rule.isCat(s)))
							// continue;
							rule.addInfo("rewriting", "true");
							filterRule(rule);
						}
					}
				}

			}
		}

		if (opts.useSpecialTokens) {
			for (String headToken : headTokens) {
				ValueFormula<NameValue> stringFormula = new ValueFormula<NameValue>(new NameValue(headToken));
				Rule specialRule = new Rule("KEYWORD_TOKEN", Lists.newArrayList(headToken),
						new ConstantFn(stringFormula));
				specialRule.addInfo("anchored", "true");
				filterRule(specialRule);
			}
		}

	}

	Set<String> RHSs = new HashSet<>();

	private boolean notSyntaxHelper(String s) {
		if (s.equals(",") || s.equals("]") || s.equals("[") || s.equals("{") || s.equals("}")) {
			return false;
		} else {
			return true;
		}
	}

	private boolean greaterScore(double currentSemScore, double currentPackingScore, double overallBestSemScore,
			double overallBestPackingScore) {
		return (currentPackingScore > overallBestPackingScore
				|| (currentPackingScore == overallBestPackingScore && currentSemScore > overallBestSemScore));
	}

	private double semanticScore(List<String> headTokens, Derivation def, Embeddings embeddings) {

		String prettyFormula = def.getFormula().prettyString();
		Set<String> noiseWords = new HashSet<>(Arrays.asList("is", "containing", "in", "item", "items"));
		String replacedCharacters = prettyFormula.replaceAll("[\\{\\}\\[\\],;]+", " ").trim();
		replacedCharacters = replacedCharacters.replaceAll("[ ]+", " ").trim();
		headTokens = headTokens.stream().filter(t -> notSyntaxHelper(t)).collect(Collectors.toList());
		String[] words = replacedCharacters.split(" ");
		List<String> formulaAsASentence = new LinkedList();
		for (int i = 0; i < words.length; ++i) {

			String singleWord = words[i];

			if (noiseWords.contains(singleWord)) {
				continue;
			}

			formulaAsASentence.add(singleWord);
		}
		double bagOfWordsSimilarity = 0.0;
		if (embeddings != null) {
			if (opts.verbose > 1) {
				LogInfo.logs("calculating similarity between %s and %s", headTokens, formulaAsASentence);
			}
			bagOfWordsSimilarity = embeddings.sentenceSimilarity(headTokens, formulaAsASentence);
		}
		if (opts.verbose > 1) {
			LogInfo.logs("bag of words similarity = %f", bagOfWordsSimilarity);
		}
		return bagOfWordsSimilarity;

	}

	private void filterRule(Rule rule) {
		if (rule.isCatUnary()) {
			LogInfo.logs("GrammarInducer.filterRule: not allowing CatUnary rules %s", rule.toString());
			return;
		}

		// if (RHSs.contains(rule.rhs.toString())) {
		// LogInfo.logs("GrammarInducer.filterRule: already have %s", rule.toString());
		// return;
		// }
		int numNT = 0;
		for (String t : rule.rhs) {
			if (Rule.isCat(t))
				numNT++;
		}

		if (numNT > GrammarInducer.opts.maxNonterminals) {
			LogInfo.logs("GrammarInducer.filterRule: too many nontermnimals (max %d) %s",
					GrammarInducer.opts.maxNonterminals, rule.rhs.toString());
			return;
		}
		if (opts.verbose > 2) {
			LogInfo.logs("filterRule - adding to induced rules: %s", rule);
		}
		inducedRules.add(rule);
		RHSs.add(rule.rhs.toString());
	}

	static Map<String, List<Derivation>> makeChartMap(List<Derivation> chartList) {
		Map<String, List<Derivation>> chartMap = new HashMap<>();
		for (Derivation d : chartList) {
			List<Derivation> derivs = chartMap.get(catFormulaKey(d));
			derivs = derivs != null ? derivs : new ArrayList<>();
			derivs.add(d);
			chartMap.put(catFormulaKey(d), derivs);
		}
		return chartMap;
	}

	// this is used to test for matches, same cat, same formula
	// maybe cat needs to be more flexible
	static String catFormulaKey(Derivation d) {
		// return d.formula.toString();
		return getNormalCat(d) + "::" + d.formula.toString();
	}

	private String varName(Derivation anchored, Derivation originalOne) {
		int s = originalOne.grammarInfo.start;
		return getNormalCat(anchored) + (anchored.start - s) + "_" + (anchored.end - s);
	}

	// when we don't want to deal with '$Color', but would rather have 'Color'
	static private String getCategoryStringFromDerivation(Derivation d) {
		return d.cat.substring(1);
	}

	static private String getNormalCat(Derivation def) {
		// return def.cat;
		// TODO : this seems like a very naive thing to do
		String cat = def.getCat();
		if (cat.endsWith("s"))
			return cat.substring(0, cat.length() - 1);
		else
			return cat;
	}

	// label the derivation tree with what it matches in chartList
	private void addMatches(Derivation deriv, Map<String, List<Derivation>> chartMap) {
		String key = catFormulaKey(deriv);
		if (chartMap.containsKey(key)) {
			deriv.grammarInfo.matches.addAll(chartMap.get(key));
			deriv.grammarInfo.matched = true;
			matches.addAll(chartMap.get(key));
		}
		for (Derivation d : deriv.children) {
			addMatches(d, chartMap);
		}
	}

	class Packing {
		List<Derivation> packing;
		double score;

		public Packing(double score, List<Derivation> packing) {
			this.score = score;
			this.packing = packing;
		}

		@Override
		public String toString() {
			return this.score + ": " + this.packing.toString();
		}
	}

	// the maximum starting index of every match that ends on or before end
	private int blockingIndex(List<Derivation> matches, int end) {
		return matches.stream().filter(d -> d.end <= end).map(d -> d.start).max((s1, s2) -> s1.compareTo(s2))
				.orElse(Integer.MAX_VALUE / 2);
	}

	// start inclusive, end exclusive
	private Packing bestPackingDP(List<Derivation> matches, int length) {

		List<Packing> bestEndsAtI = new ArrayList<>(length + 1);
		List<Packing> maximalAtI = new ArrayList<>(length + 1);
		bestEndsAtI.add(new Packing(Double.NEGATIVE_INFINITY, new ArrayList<Derivation>()));
		maximalAtI.add(new Packing(0.0, new ArrayList<Derivation>()));

		@SuppressWarnings("unchecked")
		List<Derivation>[] endsAtI = new ArrayList[length + 1];

		for (Derivation d : matches) {

			List<Derivation> derivs = endsAtI[d.end];
			derivs = derivs != null ? derivs : new ArrayList<>();
			derivs.add(d);
			endsAtI[d.end] = derivs;
		}

		for (int i = 1; i <= length; i++) {
			// the new maximal either uses a derivation that ends at i, plus a
			// previous maximal
			Packing bestOverall = new Packing(Double.NEGATIVE_INFINITY, new ArrayList<>());
			Derivation bestDerivI = null;
			if (endsAtI[i] != null) {
				for (Derivation d : endsAtI[i]) {
					double score = d.getScore() + maximalAtI.get(d.start).score;
					if (score >= bestOverall.score) {
						bestOverall.score = score;
						bestDerivI = d;
					}
				}
				List<Derivation> bestpacking = new ArrayList<>(maximalAtI.get(bestDerivI.start).packing);
				bestpacking.add(bestDerivI);
				bestOverall.packing = bestpacking;
			}
			bestEndsAtI.add(i, bestOverall);

			// or it's a previous bestEndsAtI[j] for i-minLength+1 <= j < i
			for (int j = blockingIndex(matches, i) + 1; j < i; j++) {
				if (bestEndsAtI.get(j).score >= bestOverall.score)
					bestOverall = bestEndsAtI.get(j);
			}
			if (opts.verbose > 2)
				LogInfo.logs("maximalAtI[%d] = %f: %s, BlockingIndex: %d", i, bestOverall.score, bestOverall.packing,
						blockingIndex(matches, i));
			if (bestOverall.score > Double.NEGATIVE_INFINITY)
				maximalAtI.add(i, bestOverall);
			else {
				maximalAtI.add(i, new Packing(0, new ArrayList<>()));
			}
		}
		return maximalAtI.get(length);
	}

	public List<Rule> getRules() {
		return inducedRules;
	}

	private List<Rule> induceRules(List<Derivation> packings, Derivation defDeriv) {
		List<String> RHS = getRHS(defDeriv, packings);
		SemanticFn sem = getSemantics(defDeriv, packings);
		if (opts.verbose > 2) {
			LogInfo.logs("in induce rules");
		}
		// sem will be null if type inference fails
		if (sem == null)
			return new ArrayList<>();
		String cat = getNormalCat(defDeriv);
		Rule inducedRule = new Rule(cat, RHS, sem);
		inducedRule.addInfo("induced", "true");
		inducedRule.addInfo("anchored", "true");
		List<Rule> inducedRules = new ArrayList<>();
		if (!inducedRule.isCatUnary() && !opts.nonInducingCats.contains(inducedRule.lhs)) {
			if (opts.verbose > 2) {
				LogInfo.logs("adding to inducedRUlse: %s", inducedRule);
			}
			inducedRules.add(inducedRule);
		}
		return inducedRules;
	}

	// populate grammarInfo.formula, replacing everything that can be replaced
	private void buildFormula(Derivation deriv, Map<String, String> replaceMap) {
		// LogInfo.logs("replace map: %s, derivation: %s",replaceMap.toString(),
		// deriv.toString());
		// LogInfo.logs("buildFormula. derivation %s", deriv.toString());
		// LogInfo.logs("buildFormula. derivation %s and its children %s",
		// deriv.toString(), deriv.getChildren().toString());
		if (replaceMap.containsKey(catFormulaKey(deriv))) {
			deriv.grammarInfo.formula = new VariableFormula(replaceMap.get(catFormulaKey(deriv)));
			return;
		}
		if (deriv.children.size() == 0) {
			deriv.grammarInfo.formula = deriv.formula;
		}

		for (Derivation c : deriv.children) {
			buildFormula(c, replaceMap);
		}
		Rule rule = deriv.rule;
		List<Derivation> args = deriv.children;

		// cant use the standard DerivationStream because formula is final
		if (rule == null || rule.sem == null) {
			deriv.grammarInfo.formula = deriv.formula;
		} else if (rule.sem instanceof ApplyFn) {
			Formula f = Formulas.fromLispTree(((ApplyFn) rule.sem).formula.toLispTree());
			for (Derivation arg : args) {
				if (!(f instanceof LambdaFormula))
					throw new RuntimeException("Expected LambdaFormula, but got " + f);
				Formula after = renameBoundVars(f, new HashSet<>());
				f = Formulas.lambdaApply((LambdaFormula) after, arg.grammarInfo.formula);
			}
			deriv.grammarInfo.formula = f;
		} else if (rule.sem instanceof IdentityFn) {
			deriv.grammarInfo.formula = args.get(0).grammarInfo.formula;
		} else if (rule.sem instanceof BlockFn) {
			deriv.grammarInfo.formula = new ActionFormula(((BlockFn) rule.sem).mode,
					args.stream().map(d -> d.grammarInfo.formula).collect(Collectors.toList()));
		} else {
			deriv.grammarInfo.formula = deriv.formula;
		}
	}

	private String newName(String s) {
		return s.endsWith("_") ? s : s + "_";
	}

	private Formula renameBoundVars(Formula formula, Set<String> boundvars) {
		if (formula instanceof LambdaFormula) {
			LambdaFormula f = (LambdaFormula) formula;
			boundvars.add(f.var);
			return new LambdaFormula(newName(f.var), renameBoundVars(f.body, boundvars));
		} else {
			Formula after = formula.map(new Function<Formula, Formula>() {
				@Override
				public Formula apply(Formula formula) {
					if (formula instanceof VariableFormula) { // Replace variable
						String name = ((VariableFormula) formula).name;
						if (boundvars.contains(name))
							return new VariableFormula(newName(name));
						else
							return formula;
					}
					return null;
				}
			});
			return after;
		}
	}

	private SemanticFn getSemantics(final Derivation def, List<Derivation> packings) {
		Formula baseFormula = def.grammarInfo.formula;
		if (opts.verbose > 0)
			LogInfo.logs("getSemantics %s", baseFormula);
		if (packings.size() == 0) {
			SemanticFn constantFn = new ConstantFn();
			LispTree newTree = LispTree.proto.newList();
			newTree.addChild("ConstantFn");
			newTree.addChild(baseFormula.toLispTree());
			try {
				// Type inference will throw an exception if it fails
				constantFn.init(newTree);
			} catch (RuntimeException e) {
				return null;
			}
			return constantFn;
		}

		for (int i = packings.size() - 1; i >= 0; i--) {
			baseFormula = new LambdaFormula(varName(packings.get(i), def),
					Formulas.fromLispTree(baseFormula.toLispTree()));
		}
		SemanticFn applyFn = new ApplyFn();
		LispTree newTree = LispTree.proto.newList();
		newTree.addChild("interactive.ApplyFn");
		newTree.addChild(baseFormula.toLispTree());
		applyFn.init(newTree);
		return applyFn;
	}

	private List<String> getRHS(Derivation def, List<Derivation> packings) {
		List<String> rhs = new ArrayList<>(headTokens);
		for (Derivation deriv : packings) {
			// LogInfo.logs("got (%d,%d):%s:%s", deriv.start, deriv.end,
			// deriv.formula, deriv.cat);
			rhs.set(deriv.start, getNormalCat(deriv));
			for (int i = deriv.start + 1; i < deriv.end; i++) {
				rhs.set(i, null);
			}
		}
		return rhs.subList(def.grammarInfo.start, def.grammarInfo.end).stream().filter(s -> s != null)
				.collect(Collectors.toList());
	}

	public static enum ParseStatus
	{
    Nothing, // nothing at all parses in the utterance
    /// Float, // something parse, no longer used.
    Induced, // redefining known utterance
    Core;

	public static ParseStatus fromString(String status) {
		for (ParseStatus c : ParseStatus.values())
			if (c.name().equalsIgnoreCase(status))
				return c;
		return null;
	} // define known utterance in core, should reject

	}

	public static ParseStatus getParseStatus(Example ex) {
		return getParseStatus(ex.predDerivations);
	}

	public static ParseStatus getParseStatus(List<Derivation> derivs) {
		if (derivs.size() > 0) {
			for (Derivation deriv : derivs) {
				if (deriv.allAnchored()) {
					return ParseStatus.Core;
				}
			}
			return ParseStatus.Induced;
		}
		// could check the chart here set partial, but no need for now
		return ParseStatus.Nothing;
	}

}
