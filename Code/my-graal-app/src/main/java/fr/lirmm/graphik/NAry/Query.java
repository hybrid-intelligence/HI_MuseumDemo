package fr.lirmm.graphik.NAry;

import java.util.ArrayList;

import fr.lirmm.graphik.graal.api.backward_chaining.QueryRewriter;
import fr.lirmm.graphik.graal.api.core.Atom;
import fr.lirmm.graphik.graal.api.core.AtomSet;
import fr.lirmm.graphik.graal.api.core.ConjunctiveQuery;
import fr.lirmm.graphik.graal.api.core.InMemoryAtomSet;
import fr.lirmm.graphik.graal.api.core.RuleSet;
import fr.lirmm.graphik.graal.api.core.Substitution;
import fr.lirmm.graphik.graal.api.homomorphism.HomomorphismException;
import fr.lirmm.graphik.graal.backward_chaining.pure.PureRewriter;
import fr.lirmm.graphik.graal.core.atomset.LinkedListAtomSet;
import fr.lirmm.graphik.graal.core.ruleset.LinkedListRuleSet;
import fr.lirmm.graphik.graal.homomorphism.SmartHomomorphism;
import fr.lirmm.graphik.util.stream.CloseableIterator;
import fr.lirmm.graphik.util.stream.CloseableIteratorWithoutException;
import fr.lirmm.graphik.util.stream.IteratorException;

public class Query {

	/*
	 * RuleSet negativeRuleSet = new LinkedListRuleSet(); RuleSet positiveRuleSet =
	 * new LinkedListRuleSet(); InMemoryAtomSet saturatedAtoms = new
	 * LinkedListAtomSet(); negativeRuleSet = kb.negativeConstraintSet;
	 * positiveRuleSet = kb.rules; kb.saturate(); saturatedAtoms.addAll(kb.facts);
	 * kb.unsaturate();
	 */

	/* Get answers for a conjunctive query */

	/*
	 * Gets all the atoms that satisfy a conjunctive query, it transforms the
	 * substitutions obtained using the method query(String queryString) to actual
	 * atoms.
	 * 
	 * @param queryString This is the string representing the query in dlgp format.
	 * 
	 * @param positiveRuleSet This is a set of TGDs in KBs
	 * 
	 * @param saturateAtoms This is a set of saturated atoms in KBs
	 * 
	 * @return result The sets of atoms that satisfy the query.
	 * 
	 * @exception HomomorphismException
	 * 
	 * @throws IteratorException
	 */

	public static ArrayList<AtomSet> getAnswersForCQ(ConjunctiveQuery query, RuleSet positiveRuleSet,
			InMemoryAtomSet saturatedAtoms) throws IteratorException, HomomorphismException {
		ArrayList<AtomSet> result = new ArrayList<AtomSet>();
		
		
		CloseableIterator<Substitution> substitutions = SmartHomomorphism.instance().execute(query, saturatedAtoms);
		while (substitutions.hasNext()) {
			Substitution sub = substitutions.next();
			InMemoryAtomSet atoms = sub.createImageOf(query.getAtomSet());
			result.add(atoms);
		}

		// rewrite a CQ
		/*QueryRewriter rewriter = new PureRewriter();
		CloseableIteratorWithoutException it = rewriter.execute(query, positiveRuleSet); */

		// get answers for the rewrite CQ query
		 /*while (it.hasNext()) {
			ConjunctiveQuery subQ = (ConjunctiveQuery) it.next();
			CloseableIterator<Substitution> substitutions = SmartHomomorphism.instance().execute(subQ, saturatedAtoms);
			while (substitutions.hasNext()) {
				Substitution sub = substitutions.next();
				InMemoryAtomSet atoms = sub.createImageOf(subQ.getAtomSet());
				result.add(atoms);
			}
		} */

		return result;
	}

	/*
	 * Gets all the atoms that satisfy an Instance query, it transforms the
	 * substitutions obtained using the method query(String queryString) to actual
	 * atoms.
	 * 
	 * @param query This is the string representing the query in dlgp format.
	 * 
	 * @return result The sets of atoms that satisfy the query.
	 * 
	 * @exception HomomorphismException
	 * 
	 * @throws IteratorException
	 */

	public static ArrayList<AtomSet> getAnswersForIQ(ConjunctiveQuery query, InMemoryAtomSet saturatedAtoms)
			throws IteratorException {
		ArrayList<AtomSet> result = new ArrayList<AtomSet>();
		//InMemoryAtomSet atoms = query.getAtomSet();
		//result.add(atoms.iterator().next());
		InMemoryAtomSet atoms = query.getAtomSet();
		result.add(atoms);
		return result;
	}

	public static ArrayList<AtomSet> getAnswers(ConjunctiveQuery query, RuleSet positiveRuleSet,
			InMemoryAtomSet saturatedAtoms) throws IteratorException, HomomorphismException {
		ArrayList<AtomSet> result = new ArrayList<AtomSet>();
		if (query.getAtomSet().getVariables().isEmpty()) {
			result = getAnswersForIQ(query, saturatedAtoms);
		} else
			result = getAnswersForCQ(query, positiveRuleSet, saturatedAtoms);
		return result;
	}

}
