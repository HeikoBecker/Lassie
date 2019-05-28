package edu.stanford.nlp.sempre.interactive;

import java.util.List;

import edu.stanford.nlp.sempre.Rule;
import edu.stanford.nlp.sempre.SemanticFn;

/**
 * A rule which considers the session source in determining equality
 * @author brendonboldt
 *
 */
public class SessionRule extends Rule {

  public SessionRule(String lhs, List<String> rhs, SemanticFn sem) {
    super(lhs, rhs, sem);
    // TODO Auto-generated constructor stub
  }
  
  public SessionRule(Rule rule) {
    this(rule.lhs, rule.rhs, rule.sem);
    this.source = rule.source;
  }
  
  @Override
  public boolean equals(Object o) {
    if (!super.equals(o))
      return false;
    Rule r = (Rule) o;
    return (r.source == null || this.source == null)
        || (this.source.uid.equals(r.source.uid));
  }

}
