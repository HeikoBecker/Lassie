package edu.stanford.nlp.sempre;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;

import com.fasterxml.jackson.core.type.TypeReference;

import edu.stanford.nlp.sempre.Grammar;
import edu.stanford.nlp.sempre.Json;
import edu.stanford.nlp.sempre.DictionaryEntry;

import fig.basic.LogInfo;


/**
 * Dictionary class that handles the logic of collecting the induced rules 
 * and formatting them for the Flipper dictionary
 * @author Akshal Aniche
 * Notes: uses Json.java to write the Object in JSon format
 */
public class Dictionary {
	private Dictionary() {}
	
	/**
	 * @return String JSon format of all the induced rules
	 */
	public static String jsonDictionary(String filterOnId) {
		List<DictionaryEntry> dictionary = compileDictionary(filterOnId);
		String json = Json.writeValueAsStringHard(dictionary);
		return json;
	}
	
	
	/**
	 * Reads the induced grammar and formats it into a Dictionary of DictionaryEntries
	 * Uses the function Grammar.readInducedGrammar() to read the grammar log.
	 * @return all induced rules in the grammar.log.json file in the form of
	 * 			a List<DictionaryEntry>
	 */
	private static List<DictionaryEntry> compileDictionary(String idToFilter) {
		//will contain all the dictionary entries
		List<DictionaryEntry> dictionary = new ArrayList<DictionaryEntry>();
		//read rules from grammar log
		List<String> jsonLog = Grammar.readInducedGrammar();

		for (int index = 0; index < jsonLog.size(); index++) {
			String rule = jsonLog.get(index);
			
			if(idToFilter != null) {
				String stringToLookFor = "\"uid\":\""+idToFilter+"\"";
				if ( rule.indexOf(stringToLookFor) != -1 ) {
					
					DictionaryEntry entry = filterJson(rule, index);
					dictionary.add(entry);
				}
			}
			else {
				DictionaryEntry entry = filterJson(rule, index);
				dictionary.add(entry);
			}
		}
		return dictionary;
	}
	
	/**
	 * Formats the rule read from the grammar log to only contain the 
	 * information necessary for the front end into a DictionaryEntry instance
	 * @param String line from grammar.log.json
	 * @return DictionaryEntry corresponding to the rule, with the following fields
	 * 			-right hand side of the rule (wrt the Flipper semantics)
	 * 			-ID of the user who defined it
	 * 			-head and body of the utterance from which the rule was induced
	 * 			-index, corresponds to the line number in the grammar log file
	 */
	@SuppressWarnings("unchecked")
	private static DictionaryEntry filterJson(String rule, int index) {
	    TypeReference<HashMap<String,Object>> typeRef = new TypeReference<HashMap<String,Object>>() {};
	    
	    //Read Json rule into a map
	    Map<String, Object> json = Json.readValueHard(rule, typeRef);
	    //Copy the map for the source
	    Map<String, Object> sourceMap = (Map<String, Object>) json.get("source");

	    //Collect information from the map to create the dictionary entry
	    String rhs = joinString((List<String>) json.get("rhs"), " ");
		String uid = (String) sourceMap.get("uid");
		String head = (String) sourceMap.get("head");
		String body = joinString((List<String>) sourceMap.get("body"), "; ");

		//create DictionaryEntry that corresponds to the rule
		DictionaryEntry entry = new DictionaryEntry(rhs, uid, head, body, index);
		return entry;
	}
	
	/**
	 * Joins the Strings in list using the delimiter passed as arguments
	 * @param list List of Strings to be joined
	 * @param delimiter Delimiter that separates the Strings
	 * @return Joined String
	 */
	private static String joinString(List<String> list, String delimiter) {
		String joined = "";
		String temp;
		
		ListIterator<String> iter = list.listIterator();
		
		//First token
		if (iter.hasNext())
			joined = iter.next();
		
		//join the rest of the tokens using the delimiter
		while (iter.hasNext()) {
			temp = delimiter + iter.next();
			joined = joined + temp;
		}
		
		return joined;
	}
}