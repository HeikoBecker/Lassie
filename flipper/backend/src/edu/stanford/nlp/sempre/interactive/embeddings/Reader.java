package edu.stanford.nlp.sempre.interactive.embeddings;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.HashMap;

public class Reader {
	
	private BufferedReader br;
	
	public Reader(String path) {
		File f;
		FileReader fr;
		
		try {
			f = new File(path);
			fr = new FileReader(f);
			this.br = new BufferedReader(fr);
		} catch (Exception e) {
			e.printStackTrace();
		}
		
	}
	
	public HashMap<String,Word> getWords() {
		HashMap<String,Word> words = new HashMap<>();
		try {
			while (br.ready()) {
				Word w = Word.wordFromString(br.readLine());
				words.put(w.name, w);
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
		return words;
	}
}
