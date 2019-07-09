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
	    writer.println("val _ = lassie.SEMPRE_OUTPUT := SOME (" + string.replace("\\","\\\\") + ")");
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

	// change reserved keywords in SML
	string = string.replace("\"type\":", "cmd= ");

	// force types of fields
	string = string.replace("\"NaN\"", "~1.0");

	// force-cast the result as a tactic
	string = string.replaceAll("\"value\":\"(.*?)\"","value= $1");
	
	return string;
    }
}
