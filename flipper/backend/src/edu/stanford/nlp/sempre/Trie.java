package edu.stanford.nlp.sempre;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

/**
 * Used to access or delete rules efficiently by walking down their RHS.
 * Stores all rules we are currently using
 * @author Percy Liang
 */
public class Trie {
  public ArrayList<Rule> rules = new ArrayList<>();
  
  // list of rules where String appears on the RHS
  public Map<String, Trie> children = new LinkedHashMap<>();
  // Set of LHS categories of all rules in this subtree
  public Set<String> cats = new LinkedHashSet<>();

  public Trie next(String item) { return children.get(item); }

  public void add(Rule rule) { add(rule, 0); }
  
  private void add(Rule rule, int i) {
    cats.add(rule.lhs);

    if (i == rule.rhs.size()) {
      if (!rules.contains(rule)) // filter exact match
        rules.add(rule);
      return;
    }

    String item = rule.rhs.get(i);
    Trie child = children.get(item);
    if (child == null)
      children.put(item, child = new Trie());
    child.add(rule, i + 1);
  }

  /** Method to delete a rule from the Trie
   * @author Akshal Aniche
   * @param rule
   */
  public void remove(Rule rule){ remove(rule, 0); }
  
  /** Helper method to recursively traverse the trie and delete the specified rule with clean up in a bottom up strategy
   * @author Akshal Aniche
   * @param rule
   * @param i
   */
  private void remove(Rule rule, int i) {
	  //filter and delete exact match
	  if (i == rule.rhs.size()) {
		  if (rules.contains(rule)) {
			  rules.remove(rule);
		  } else {
			  throw new IllegalArgumentException("You can't delete a rule that doesn't exist.");
		  }
	  }
	  else {
		  String item = rule.rhs.get(i);
		  Trie child = children.get(item);
		  if (child == null) {
			  throw new IllegalArgumentException("You can't delete a rule that doesn't exist.");
		  }
		  child.remove(rule, i + 1);
		  
		  if(child.isEmpty()) { //All of the rules in child and its descendant have been deleted
			  children.remove(item); //delete the child from the trie
		  }
	  }
	  if (!catExists(rule.lhs)) { //remove the lhs of the rule from cats if that was the only rule of the specified category
		  cats.remove(rule.lhs);
	  }
	  return;
	  
  }
  
  /** Check whether a rule in the Trie has the same lhs as the given String (i.e. is of the given category)
   * @author Akshal Aniche
   * @param cat
   * @return true iff there exists a rule in rules with lhs==cat or there exists a rule in children with lhs==cat 
   */
  private boolean catExists(String cat) {
	  Iterator<Rule> iter = rules.iterator();  
	  while (iter.hasNext()) {
		  Rule rule = iter.next();
		  if (cat.equals(rule.lhs)) { 	//there is a rule of the given category
			  return true;		
		  }
	  }
	  boolean result = false; 			//there is no rule of the given category in the ArrayList
	  
	  //Need to check if the category exists in one of the children
	  for (Trie child : children.values()) {
		  result = result || child.catExists(cat); //compile the result from all the descendants
	  }
	  
	  return result;
  }
  

  /** Checks whether a Trie is empty 
   * @author Akshal Aniche
   * @return true iff the ArrayList of rules of the Trie is empty and the arrayList of rules of each of its descendant is empty
   */
  public boolean isEmpty() {
	  boolean result = this.rules.isEmpty();	//initial choice
	  for (Trie child : children.values()) {
		  result = result && child.isEmpty(); 	//compile the result from all the descendants
	  }
	  return result;
  }
  
  public String toString(){
	  String s = "rules: "+rules.toString()+"\n";
	  for (Map.Entry<String, Trie> entry : children.entrySet()){
		  s = s + "mapKey = "+entry.getKey();
		  s = s + "\t "+entry.getValue().toString()+"\n";
	  }
	  return s;
  }
}
