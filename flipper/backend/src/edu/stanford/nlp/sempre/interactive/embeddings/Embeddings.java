package edu.stanford.nlp.sempre.interactive.embeddings;

import java.util.List;
import java.util.stream.Collectors;
import java.util.ArrayList;
import fig.basic.LogInfo;

public class Embeddings {

	Dictionary dict;
	int vectorSize;
	
	/**
	 * Returns the dot product of the two vectors
	 */
	static double dot(List<Double> l1, List<Double> l2) {
		if (l1.size() != l2.size())
			throw new IllegalArgumentException("The two vectors need to have the same dimension in a similarity computation.");
		double sum = 0.0;
		for (int i = 0; i < l1.size(); ++i)
			sum += l1.get(i) * l2.get(i);
		return sum;
	}
	
	/**
	 * Returns the cosine similarity between the two Words specified
	 */
	public double sim(Word w1, Word w2) {
		if (w1.scalars == null || w2.scalars == null) 
			throw new IllegalArgumentException ("You cannot have one word vector be null in a similarity computation");
		return dot(w1.scalars, w2.scalars)/(w1.mag() * w2.mag());
	}
	
	private Word sumOfWords(Word w1, Word w2) {
		if (w1.scalars.size() != w2.scalars.size()) {
			throw new IllegalArgumentException("The two vectors need to have the same dimension in a similarity computation.");
		}
		Word sum = Word.zeroWordLike("--sumOfWords--", w1);
		
		// HERE IS THE PROBLEM - IT JUST ADDS TO A NEW PLACE
		for (int i = 0; i < w1.scalars.size(); ++i) {
			sum.scalars.set(i, w1.scalars.get(i) + w2.scalars.get(i));
		}
		return sum;
	}
	
	private Word divideWordByScalar(Word w, double c) {		
		Word resultWord = Word.zeroWordLike("--default--", w);
		resultWord.scalars = w.scalars.stream().map(s -> s / c).collect(Collectors.toCollection(ArrayList::new));
		return resultWord;
	}
	
	public Embeddings(String embeddingsPath) {
		Reader reader = new Reader(embeddingsPath);
		this.dict = new Dictionary(reader);
		this.vectorSize = dict.entries.getOrDefault("the", Word.nullWord).scalars.size();
		LogInfo.logs("vector size = %d", vectorSize);
		
	}
	
	/**
	 * Returns a Word (word vector representation) corresponding to the String word passed as argument
	 */
	public Word getWord (String word) {
		Word zeroWord = Word.zeroWordOfSize(this.vectorSize);
		return dict.entries.getOrDefault(word, zeroWord);
	}
	
	public Word averageWord(List<String> sentence) {
		Word startingWord = getWord(sentence.get(0));
		Word sum = startingWord;
		for (int i = 1; i < sentence.size(); ++i) {
			sum = sumOfWords(sum, getWord(sentence.get(i)));
		}
		Word average = divideWordByScalar(sum, (double)sentence.size());
		return average;
		
	}
	
	public double sentenceSimilarity(List<String> s1, List<String> s2) {
		Word w1 = averageWord(s1);
		Word w2 = averageWord(s2);
		return sim(w1, w2);
	}
}