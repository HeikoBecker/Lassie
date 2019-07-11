package edu.stanford.nlp.sempre.interactive.lassie;

import com.google.common.base.Joiner;
import com.google.common.base.Strings;
import com.google.common.collect.Lists;

import com.fasterxml.jackson.core.JsonProcessingException;

import edu.stanford.nlp.sempre.*;
import fig.basic.*;
import java.util.*;
import java.io.*;


public class LassieUtils{
    
    public static void printToSocket(String string) {
	try (PrintWriter writer = new PrintWriter("interactive/sempre-out-socket.sml", "UTF-8")) {
	    writer.println("val _ = Lassie.SEMPRE_OUTPUT := SOME (" + string + ")");
	    writer.close();
	} catch (IOException ex) {
	    System.err.println("Error writing to file interactive/sempre-out-socket.sml");
	}
    }

    // Rudimentary translation of a json object into an SML record
    public static String json2sml(String string) {
	// dependent on knowing the fields
	List<String> fields = Lists.newArrayList("candidates", "score", "prob", "anchored", "formula",
						 "stats", "size", "status", "lines");
	// unquote fields; subsitute `:` for `=`
	for (String field : fields) {
	    string = string.replace("\"" + field + "\":", field + "= ");
	}

	string =
	    string
	    .replace("\"type\":", "cmd= ") // avoid reserved keywords of SML
	    .replace("\"NaN\"", "~1.0") // force types of fields
	    .replaceAll("\"value\":\"(.*?)\"","value= \"$1\",tactic= $1"); // cast the value as a tactic
	
	return string;
    }
}
