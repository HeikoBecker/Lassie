package edu.stanford.nlp.sempre.interactive.embeddings;

import java.util.HashMap;

public class Dictionary {
	
  HashMap<String,Word> entries;
	
	public Dictionary(Reader r) {
		this.entries = r.getWords(); 
	}
}
