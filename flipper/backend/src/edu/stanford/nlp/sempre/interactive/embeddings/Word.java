package edu.stanford.nlp.sempre.interactive.embeddings;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public class Word {
	
  public static final Word nullWord = new Word("NULL_WORD", null);
  
  
	ArrayList<Double> scalars;
	final String name;
	
	/**
	 * Create an arbitrary word corresponding to a zero vector with
	 * the same dimensions as a given word.
	 * @param name
	 * @param like
	 * @return
	 */
	public static Word zeroWordLike(String name, Word like) {
	  ArrayList<Double> zeros =
	      new ArrayList<>(Collections.nCopies(like.scalars.size(), 0.0));
	  return new Word(name, zeros);
	}
	
	
	
	public static Word zeroWordOfSize(int n) {
		ArrayList<Double> zeros =
			      new ArrayList<>(Collections.nCopies(n, 0.0));
			  return new Word("--default--", zeros);
		
	}
	
	public static Word wordFromString(String line) {
		String[] vals = line.split(" ");
		String name = vals[0];
		ArrayList<Double> scalars = new ArrayList<>();
		for (int i = 1; i < vals.length; ++i) {
			scalars.add(Double.valueOf(vals[i]));
		}
		return new Word(name, scalars);
	}
	
	public Word(String name, ArrayList<Double> scalars) {
		this.name = name;
		this.scalars = scalars;
	}
	
	public Word(ArrayList<Double> scalars) {
		 this("--default--", scalars);
	}
	
	public List<Double> unitVector() {
		ArrayList<Double> l = new ArrayList<>();
		double mag = this.mag();
		for (Double x : scalars)
			l.add(x/mag);
		return l;
	}
	
	
	public double mag() {
		if (scalars == null) 
			return 0.0;
		return Math.pow(scalars.stream()
				.reduce(0.0, (a,b) -> a + b*b), 0.5);
	}
	
	public String toString() {
		return name;
	}
}
