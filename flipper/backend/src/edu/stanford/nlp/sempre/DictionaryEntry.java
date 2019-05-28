package edu.stanford.nlp.sempre;

import com.fasterxml.jackson.annotation.JsonProperty;

/**
 * A DictionaryEntry represents a single induced rule in the Dictionary class 
 * after trimming it to the information necessary for Flipper.
 * @author Akshal Aniche
 *
 */
public class DictionaryEntry {
	@JsonProperty
	public String rhs;  // Right-hand side of the rule: sequence of categories (have $ prefix) and tokens.
			
	@JsonProperty
	public String uid;  // User ID of the user who defined the rule
			
	@JsonProperty
	public String head;	// Head of the initial definition
			
	@JsonProperty
	public String body;	// Body of the initial definition 
	
	@JsonProperty
	public int index; 	//Line number in the grammar log
	//Can be used to reference for deleting
			
	public DictionaryEntry(String rhs, String uid, String head, String body, int index) {
		this.rhs = rhs;
		this.uid = uid;
		this.head = head;
		this.body = body;
		this.index = index;
	}
}
