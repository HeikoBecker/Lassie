package edu.stanford.nlp.sempre.interactive;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import fig.basic.LogInfo;

import edu.stanford.nlp.sempre.Example;
import edu.stanford.nlp.sempre.Params;
import edu.stanford.nlp.sempre.ParserState;
import edu.stanford.nlp.sempre.Rule;
import edu.stanford.nlp.sempre.Trie;

/**
 * A parser which filters rules originating from a different session
 * @author brendonboldt
 * This class should only be used for testing purposes.
 */
public class SessionBeamParser extends InteractiveBeamParser {

  public SessionBeamParser(Spec spec) {
    super(spec);
  }

  @Override
  public synchronized void addRule(Rule rule) {
    SessionRule sRule = new SessionRule(rule);
    sRule.setInfo(rule);
    
    allRules.add(sRule);

    if (!rule.isCatUnary()) {
      trie.add(sRule);
    } else {
      interactiveCatUnaryRules.add(sRule);
    }
  }
  
  @Override
  public ParserState parse(Params params, Example ex, boolean computeExpectedCounts) {
    String sessionId = ex.id;
    // Make a copy of the original set of rules
    List<Rule> oldInteractiveCatUnaryRules = this.catUnaryRules;
    Trie oldTrie = this.trie;
    Set<Rule> oldAllRules = this.allRules;
    this.interactiveCatUnaryRules = new ArrayList<>();
    this.trie = new Trie();
    this.allRules = new LinkedHashSet<>();
    // Repopulate current rules filtering by session
    for (Rule r : oldAllRules) {
      if (r.source == null || sessionId.equals(r.source.uid)) {
         this.addRule(r);
      }
    }

    ParserState state = super.parse(params, ex, computeExpectedCounts);

    // Restore original set of rules
    this.interactiveCatUnaryRules = oldInteractiveCatUnaryRules;
    this.trie = oldTrie;
    this.allRules = oldAllRules;

    return state;
  }

}
