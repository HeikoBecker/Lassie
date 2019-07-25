package edu.stanford.nlp.sempre.interactive.lassie;

import java.io.IOException;
import java.io.PrintWriter;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import com.google.common.collect.Sets;

import edu.stanford.nlp.sempre.ContextValue;
import edu.stanford.nlp.sempre.Json;
import edu.stanford.nlp.sempre.NaiveKnowledgeGraph;
import edu.stanford.nlp.sempre.StringValue;
import edu.stanford.nlp.sempre.interactive.Item;
import edu.stanford.nlp.sempre.interactive.World;

import fig.basic.IOUtils;
import fig.basic.LogInfo;
import fig.basic.Option;

import edu.stanford.nlp.sempre.interactive.lassie.Component;

// the world of tactics
public class TacticWorld extends World {

    public static class Options {
	@Option(gloss = "Path to database file, contains components and their features")
	public String dbPath = null;
	@Option(gloss = "Path to lexicon file, temporary interface to inform SimpleLexiconFn of db")
	public String lexPath = null;
	// @Option(gloss = "Path to seed grammar, to be instantiated to all types")
	// public String seedGrammarPath = null;
	// @Option(gloss = "Path to generated grammar, result of generation from seed")
	// public String genGrammarPath = null;
    }
    public static Options opts = new Options();
    
    public String string; // string in construction
    public Map<String,Set<String>> entities; // component -> features
    public Map<String,Set<String>> features; // feature -> components
    
    @SuppressWarnings("unchecked")
    public TacticWorld() {
	this.allItems = new HashSet<>();
	this.selected = new HashSet<>();
	this.previous = new HashSet<>();
	this.entities = new HashMap<String,Set<String>>();
	this.features = new HashMap<String,Set<String>>();
	readDB();
	writeLexicon();
    }

    
    private void logLine(String path, String line) {
	PrintWriter out;
	try {
	    out = IOUtils.openOutAppend(path);
	    out.println(line);
	    out.close();
	} catch (IOException e) {
	    // TODO Auto-generated catch block
	    e.printStackTrace();
	}
    }
    
    private void insert(String component, Set<String> features) {
	for (String feat : features) {
	    //LogInfo.logs("inserting: %s, %s, %s", component, attribute, feat);
	    insert(component, feat);
	}
    }
    private void insert(String component, String feature) {
	// From components to their features
	this.entities.putIfAbsent(component, new HashSet<String>());
	Set<String> componentFeatures = this.entities.get(component);
	componentFeatures.add(feature);
	this.entities.put(component, componentFeatures);
	// From features to components which possess them
	this.features.putIfAbsent(feature, new HashSet<String>());
	Set<String> components = this.features.get(feature);
	components.add(component);
	//LogInfo.logs("  adding: %s :: %s", feature, component);
	this.features.put(feature, components);
    }
    
    private void readDB() {
	LogInfo.begin_track("TacticWorld.readEntities: %s", opts.dbPath);
	// Load up from database
	for (String line : IOUtils.readLinesHard(opts.dbPath)) {
	    //LogInfo.logs("Processing line: %s", line);
	    if (line.startsWith("#")) continue; // Skip comment lines
	    String[] statements = line.split(",\\s*");
	    String[] tokens = statements[0].split("\\s+");
	    if (tokens.length == 0 || tokens[0].equals("")) continue; // Skip empty lines
	    // We expect triplets (at least), e.g. "POW_2 feature.name feature.name.power"
	    if (tokens.length >= 3) {  
		String component = tokens[0];
		String attribute = tokens[1];
		String feature = attribute + "." + tokens[2];
		for (int i = 3; i < tokens.length; i++)
		    feature = feature + " " + tokens[i];
		Set<String> moreFeatures = new HashSet();
		moreFeatures.add(feature);
		for (int i = 1; i < statements.length; i++)
		    moreFeatures.add(attribute + "." + statements[i].replaceAll("\\s+", " "));
		insert(component, moreFeatures);
	    } else {
		throw new RuntimeException("Unhandled: " + line);
	    }
	}
	LogInfo.end_track();
    }

    private String typeOf(String c) {
	for (String f : entities.get(c))
	    if (f.startsWith("type.")) return f.replace(" ","");
	throw new RuntimeException("Cannot find type: " + c);
    }
    
    private String suffix(String f) {
	try {
	    return f.substring(f.lastIndexOf('.') + 1, f.length());
	} catch (Exception e) {
	    throw new RuntimeException("Bad string: " + f);
	}
    }
    
    private String prefix(String f) {
	try {
	    return f.substring(0, f.lastIndexOf('.'));
	} catch (Exception e) {
	    throw new RuntimeException("Bad string: " + f);
	} 
    }

    private String quot(String s) { return "\"" + s + "\""; }
    
    private void writeLexicon() {
	try {
	    PrintWriter writer = new PrintWriter(opts.lexPath, "UTF-8");
	    // Components (literal)
	    for (String c : this.entities.keySet()) {
		Map<String, Object> jsonMap = new LinkedHashMap<>();
		jsonMap.put("lexeme", c);
		jsonMap.put("formula", quot(c)); // force Formula to StringFormula in the Lisp interpreter
		jsonMap.put("type", suffix(typeOf(c)));
		writer.println(Json.writeValueAsStringHard(jsonMap));
	    }
	    // Features
	    for (String f : this.features.keySet()) {
		Map<String, Object> jsonMap = new LinkedHashMap<>();
		jsonMap.put("lexeme", suffix(f));
		jsonMap.put("formula", quot(f)); // may contain spaces, force Formula to StringFormula
		jsonMap.put("type", prefix(f));
		writer.println(Json.writeValueAsStringHard(jsonMap));
	    }
	    writer.close();
	} catch (IOException e) {
	    throw new RuntimeException("Error writing to file " + opts.lexPath);
	}
    }

    // private void generateGrammar() {
    // 	Set<String> types = new HashSet<String>();
    // 	for (String f : this.features)
    // 	    if (f.startsWith("type."))
    // 		types.add(f);
    // 	String monotypeRules = 
    // 	for (String t : types) {
    // 	}	    
    // }
    
    // String constructions, basically tactic language
    public String int2string(Integer n) {
	return n.toString();
    }
    public String app(String fn, String arg) {
	if (fn.equals("") || arg.equals("")) return "";
	return fn + " " + arg;
    }
    public String then(String tac1, String tac2) {
	if (tac1.equals("") || tac2.equals("")) return "";
	return tac1 + " \\ " + tac2;
    }
    public String then1(String tac1, String tac2) {
	if (tac1.equals("") || tac2.equals("")) return "";
	return tac1 + " >- " + parens(tac2);
    }
    public String cons(String hd, String tl) {
	if (hd.equals("") || tl.equals("")) return "";
	return hd + "," + tl;
    }
    public String list(String seq) {
	if (seq.equals("")) return "";
	return "[" + seq + "]";
    }
    public String quote(String exp) {
	if (exp.equals("")) return "";
	return "`" + exp + "`";
    }
    public String parens(String exp) {
	if (exp.equals("")) return "";
	return "(" + exp + ")";
    }
    public String op(String operator, String arg1, String arg2) {
	if (operator.equals("") || arg1.equals("") || arg2.equals("")) return "";
	return arg1 + " " + operator + " " + arg2;
    }

    // Feature manipulations
    public static String refine(String s1, String s2) {
	return s1 + "." + s2;
    }
    public Set<String> fromFeature(String f) {
	if (f.equals("top")) return entities.keySet();
	else if (f.equals("bot")) return new HashSet<String>();
        else if (features.containsKey(f)) return features.get(f);
	else throw new RuntimeException("Feature not recognized: " + f);
    }
    
    // Set operations
    public Set<String> intersect(Set<String> s1, Set<String> s2) {
	return s1.stream().filter(i -> s2.contains(i)).collect(Collectors.toSet());
    }

    public String set2string(Set<String> s) {
	return String.join(",", s);
    }

    /*
     * DALExecutor always expects an ActionFormula, and only executes
     * other Formulas (e.g. CallFormulas) as sub-formulas of the main
     * one. Action formulas appear in the grammar as (: myAction arg1
     * arg2 ...), the return value is not observed and instead taken
     * from the toJSON() method.
     */
    
    // Result
    public void tacReturn(String str) {
	if (str.equals("")) this.string = "NO_TAC";	
	else this.string = str;
    }

    public void strReturn(String str) {
	this.string = str;
    }

    // Called from DALExecutor after evaluation; is the return value of executor
    public String toJSON() {
	return this.string;
    }

    ///////////////////////////////
    // UNUSED, required by interface
    @Override
    public Set<Item> has(String rel, Set<Object> values) {
	// LogInfo.log(values);
	return this.allItems.stream().filter(i -> values.contains(i.get(rel))).collect(Collectors.toSet());
    }
    @Override
    public Set<Object> get(String rel, Set<Item> subset) {
	return subset.stream().map(i -> i.get(rel)).collect(Collectors.toSet());
    }
    @Override
    public void update(String rel, Object value, Set<Item> selected) {}
    @Override
    public void merge() {}
    ///////////////////////////////
}
