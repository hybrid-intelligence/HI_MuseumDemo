package fr.lirmm.graphik.NAry;

import fr.lirmm.graphik.graal.api.forward_chaining.AbstractChase;
import fr.lirmm.graphik.graal.api.core.AtomSet;
import fr.lirmm.graphik.graal.api.core.ConjunctiveQuery;
import fr.lirmm.graphik.graal.api.core.InMemoryAtomSet;
import fr.lirmm.graphik.graal.api.core.Predicate;
import fr.lirmm.graphik.graal.api.core.Rule;
import fr.lirmm.graphik.graal.api.forward_chaining.AbstractChase;
import fr.lirmm.graphik.graal.api.forward_chaining.ChaseException;
import fr.lirmm.graphik.graal.api.forward_chaining.ChaseHaltingCondition;
import fr.lirmm.graphik.graal.api.forward_chaining.RuleApplier;
import fr.lirmm.graphik.graal.api.homomorphism.Homomorphism;
import fr.lirmm.graphik.graal.core.DefaultRule;
import fr.lirmm.graphik.graal.core.ruleset.IndexedByBodyPredicatesRuleSet;
import fr.lirmm.graphik.graal.forward_chaining.rule_applier.DefaultRuleApplier;
import fr.lirmm.graphik.util.profiler.*;
import fr.lirmm.graphik.util.Verbosable;
import java.util.Set;
import java.util.TreeSet;

public class DefaultChase extends AbstractChase
	implements Verbosable
	{
	  private IndexedByBodyPredicatesRuleSet ruleSet;
	  private AtomSet atomSet;
	  private boolean isVerbose = false;
	  private Set<Rule> rulesToCheck;
	  private Set<Rule> nextRulesToCheck;

	  public DefaultChase(Iterable<Rule> rules, AtomSet atomSet)
	  {
	    this(rules, atomSet, new DefaultRuleApplier());
	  }

	  public DefaultChase(Iterable<Rule> rules, AtomSet atomSet, RuleApplier ruleApplier)
	  {
	    super(ruleApplier);
	    this.atomSet = atomSet;
	    this.ruleSet = new IndexedByBodyPredicatesRuleSet();
	    init(rules);
	  }

	  public DefaultChase(Iterable<Rule> rules, AtomSet atomSet, Homomorphism<ConjunctiveQuery, AtomSet> solver)
	  {
	    this(rules, atomSet, new DefaultRuleApplier(solver));
	  }

	  public DefaultChase(Iterable<Rule> rules, AtomSet atomSet, ChaseHaltingCondition haltingCondition) {
	    this(rules, atomSet, new DefaultRuleApplier(haltingCondition));
	  }

	  public DefaultChase(Iterable<Rule> rules, AtomSet atomSet, Homomorphism<ConjunctiveQuery, AtomSet> solver, ChaseHaltingCondition haltingCondition)
	  {
	    this(rules, atomSet, new DefaultRuleApplier(solver, haltingCondition));
	  }

	  private void init(Iterable<Rule> rules) {
	    int i = 0;
	    this.nextRulesToCheck = new TreeSet();
	    for (Rule r : rules) {
	      Rule copy = new DefaultRule(r);
	      copy.setLabel(Integer.toString(++i));
	      this.ruleSet.add(copy);
	      this.nextRulesToCheck.add(copy);
	    }
	  }

	  public void next()
	    throws ChaseException
	  {
	    this.rulesToCheck = this.nextRulesToCheck;
	    this.nextRulesToCheck = new TreeSet();
	    try {
	      if (!this.rulesToCheck.isEmpty()) {
	        if (getProfiler().isProfilingEnabled()) {
	          getProfiler().start("saturationTime");
	        }
	        for (Rule rule : this.rulesToCheck) {
	          String key = null;
	          if ((this.isVerbose) && (getProfiler().isProfilingEnabled())) {
	            key = "Rule " + rule.getLabel() + " application time";
	            getProfiler().clear(key);
	            getProfiler().trace(new String[] { rule.toString() });
	            getProfiler().start(key);
	          }
	          if (getRuleApplier().apply(rule, this.atomSet)) {
	            for (Predicate p : rule.getHead().getPredicates()) {
	              for (Rule r : this.ruleSet.getRulesByBodyPredicate(p)) {
	                this.nextRulesToCheck.add(r);
	              }
	            }
	          }
	          if ((this.isVerbose) && (getProfiler().isProfilingEnabled())) {
	            getProfiler().stop(key);
	          }
	        }
	        if (getProfiler().isProfilingEnabled())
	          getProfiler().stop("saturationTime");
	      }
	    }
	    catch (Exception e) {
	      throw new ChaseException("An error occured during saturation step.", e);
	    }
	  }

	  public boolean hasNext()
	  {
	    return !this.nextRulesToCheck.isEmpty();
	  }

	  public void enableVerbose(boolean enable)
	  {
	    this.isVerbose = enable;
	  }

}
