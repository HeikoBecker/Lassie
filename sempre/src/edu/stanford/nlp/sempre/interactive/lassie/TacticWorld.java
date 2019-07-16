package edu.stanford.nlp.sempre.interactive.lassie;

import java.util.List;
import java.util.LinkedList;
import java.util.Set;
import java.util.HashSet;
import java.util.Map;
import java.util.HashMap;
import java.util.Arrays;
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
import fig.basic.Option;
import fig.basic.LogInfo;

import edu.stanford.nlp.sempre.interactive.lassie.Component;

// the world of tactics
public class TacticWorld extends World {

    public static class Options {
	@Option(gloss = "Path to database file, contains components and their features")
	public String dbPath = null;
    }
    
    public static Options opts = new Options();
    
    public String constructedTactic;
    public Map<String,Map<String,Set<String>>> entities; // component (name) -> feature -> values
    public Map<String,Set<String>> features; // feature -> components (name)
    
    @SuppressWarnings("unchecked")
    public TacticWorld() {
	this.allItems = new HashSet<>();
	this.selected = new HashSet<>();
	this.previous = new HashSet<>();
	this.entities = new HashMap< String, Map<String,Set<String>> >();
	this.features = new HashMap<String,Set<String>>();
	readDB();
    }
    
    private void insert(String component, String feature, Set<String> values) {
	for (String val : values) insert(component, feature, val);
    }
    private void insert(String component, String feature, String value) {
	// From components to their features
	entities.putIfAbsent(component, new HashMap<String,Set<String>>());
	Map<String,Set<String>> features = entities.get(component);
	features.putIfAbsent(feature, new HashSet<String>());
	Set<String> values = features.get(feature);
	values.add(value);
	features.put(feature, values);
	entities.put(component, features);
	// From features to components which satisfy them
	features.putIfAbsent(feature, new HashSet<String>());
	Set<String> components = features.get(feature);
	components.add(component);
	features.put(feature, components);
    }
    
    private void readDB() {
	LogInfo.begin_track("TacticWorld.readEntities: %s", opts.dbPath);
	// Load up from database
	for (String line : IOUtils.readLinesHard(opts.dbPath)) {
	    if (line.startsWith("#")) continue; // Skip comment lines
	    String[] tokens = line.split("\\s");
	    // We expect triplets, e.g. "POW_2 feature.name feature.name.power"
	    if (tokens.length >= 3) {  
		String component = tokens[0];
		String feature = tokens[1];
		Set<String> values = new HashSet();
		for (int i = 2; i < tokens.length; i++)
		    values.add(tokens[i]);
		insert(component, feature, values);
	    } else {
		throw new RuntimeException("Unhandled: " + line);
	    }
	}
	LogInfo.end_track();
    }
    
    // String constructions
    public String int2string(Integer n) {
	return n.toString();
    }
    public String app(String fn, String arg) {
	return fn + " " + arg;
    }
    public String then(String tac1, String tac2) {
	return tac1 + " \\ " + tac2;
    }
    public String then1(String tac1, String tac2) {
	return tac1 + " >- " + tac2;
    }
    public String cons(String hd, String tl) {
	return hd + ", " + tl;
    }
    public String list(String seq) {
	return "[" + seq + "]";
    }
    public String quote(String exp) {
	return "`" + exp + "`";
    }
    public String parens(String exp) {
	return "(" + exp + ")";
    }
    public String op(String operator, String arg1, String arg2) {
	return arg1 + " " + operator + " " + arg2;
    }

    // Feature manipulations
    public static String refine(String s1, String s2) {
	return s1 + "." + s2;
    }
    // this does e.g. feature.name.fs -> feature.name
    public static String typeOf(String s1) { 
	String[] addr = s1.split("\\.");
	return String.join(".",Arrays.copyOfRange(addr, 0, addr.length - 2));
    }
    public Set<String> fromFeature(String f) {
	if (f == "top") return entities.keySet();
	else if (f == "bot") return new HashSet<String>();
        else if (features.containsKey(f)) return features.get(f);
	else throw new RuntimeException("Feature not recognized: " + f);
    }
    
    // Set operations
    public Set<String> filter(Set<String> s1, Set<String> s2) {
	return s1.stream().filter(i -> s2.contains(i)).collect(Collectors.toSet());
    }
    public Set<String> filter(Set<String> s1, String s2) {
	if (s2 == "top") return s1;
	else if (s2 == "bot") return new HashSet<String>();
	else return s1.stream().filter(i -> features.get(s2).contains(i)).collect(Collectors.toSet());
    }
    public Set<String> filter(String s1, Set<String> s2) {
	return filter(s2,s1);
    }
    public Set<String> filter(String s1, String s2) {
	if (s1 == "bot" || s2 == "bot") return new HashSet<String>();
	else if (s1 == "top") return fromFeature(s2);
	else if (s2 == "top") return fromFeature(s1);
	else return filter(fromFeature(s1),fromFeature(s2));
    }
	

    // Result
    public void tacReturn(String str) { this.constructedTactic = str; }
    
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

    // Called from DALExecutor after evaluation; is the return value of executor
    public String toJSON() {
	return this.constructedTactic;
    }
    
}
