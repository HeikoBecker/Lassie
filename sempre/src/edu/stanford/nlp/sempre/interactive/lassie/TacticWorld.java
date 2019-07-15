package edu.stanford.nlp.sempre.interactive.lassie;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
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
import fig.basic.Option;

// the world of tactics
public class TacticWorld extends World {

    // @SuppressWarnings("unchecked")
    // public TacticWorld(Set<Item> tactics) {
    // 	super();
    // 	this.allItems = tactics;
    // }

    public String returnString;
    
    @SuppressWarnings("unchecked")
    public TacticWorld() {
    	super();
    }

    public String int2string(Integer n) { return n.toString(); }
    public String app(String fn, String arg) { return fn + " " + arg; }
    public String then(String tac1, String tac2) { return tac1 + " \\ " + tac2; }
    public String then1(String tac1, String tac2) { return tac1 + " >- " + tac2; }
    public String cons(String hd, String tl) { return hd + ", " + tl; }
    public String list(String seq) { return "[" + seq + "]"; }
    public String quote(String exp) { return "`" + exp + "`"; }
    public String parens(String exp) { return "(" + exp + ")"; }
    public String op(String operator, String arg1, String arg2) { return arg1 + " " + operator + " " + arg2; }
    
    public void tacReturn(String str) { this.returnString = str; }
    
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
	return this.returnString;
    }
    
}
