package edu.stanford.nlp.sempre.interactive;

import edu.stanford.nlp.sempre.Master;
import edu.stanford.nlp.sempre.interactive.InteractiveUtils.AuthorDescription;

public class QueryStats {
  Master.Response response;
  QueryType type;

  public enum QueryType {
    q, def, accept, reject, other, dictionary
  };

  public QueryStats(Master.Response response) {
    this.response = response;
  }

  public QueryStats(Master.Response response, String command) {
    this.response = response;
    put("type", command.substring(1));
  }

  public void put(String k, Object v) {
    response.stats.put(k, v);
  }

  public void size(int num) {
    put("size", num);
  }

  public void status(String status) {
    put("status", status);
  }

  public void rank(int r) {
    put("rank", r);
  }

  public void error(String msg) {
    put("error", msg);
  }
  
  public void author(AuthorDescription authorDescription) {
	  put("author", authorDescription);
  }
}
