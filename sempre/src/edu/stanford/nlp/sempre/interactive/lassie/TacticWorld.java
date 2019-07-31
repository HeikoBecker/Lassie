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
public class TacticWorld {

    // String constructions, basically tactic language
    public static String int2string(Integer n) {
	return n.toString();
    }
    public static String app(String fn, String arg) {
	if (fn.equals("") || arg.equals("")) return "";
	return fn + " " + arg;
    }
    public static String then(String tac1, String tac2) {
	if (tac1.equals("") || tac2.equals("")) return "";
	return tac1 + " \\ " + tac2;
    }
    public static String then1(String tac1, String tac2) {
	if (tac1.equals("") || tac2.equals("")) return "";
	return tac1 + " >- " + parens(tac2);
    }
    public static String cons(String hd, String tl) {
	if (hd.equals("") || tl.equals("")) return "";
	return hd + "," + tl;
    }
    public static String list(String seq) {
	if (seq.equals("")) return "";
	return "[" + seq + "]";
    }
    public static String quote(String exp) {
	if (exp.equals("")) return "";
	return "`" + exp + "`";
    }
    public static String parens(String exp) {
	if (exp.equals("")) return "";
	return "(" + exp + ")";
    }
    public static String op(String operator, String arg1, String arg2) {
	if (operator.equals("") || arg1.equals("") || arg2.equals("")) return "";
	return arg1 + " " + operator + " " + arg2;
    }

    // Feature manipulations
    public static String refine(String s1, String s2) {
	return s1 + "." + s2;
    }
    public static Set<String> fromFeature(String f) {
	// needs to stay static for the JavaExecutor;
	// current fix to keep this method static: create new world at each call;
	// very inefficient
	HOLOntology ontology = HOLOntology.getTheOntology(); 
	if (f.equals("top")) return ontology.entities.keySet();
	else if (f.equals("bot")) return new HashSet<String>();
        else if (ontology.features.containsKey(f)) return ontology.features.get(f);
	else throw new RuntimeException("Feature not recognized: " + f);
    }
    
    // Set operations
    public static Set<String> intersect(Set<String> s1, Set<String> s2) {
	return s1.stream().filter(i -> s2.contains(i)).collect(Collectors.toSet());
    }

    public static String set2string(Set<String> s) {
	return String.join(",", s);
    }
}
