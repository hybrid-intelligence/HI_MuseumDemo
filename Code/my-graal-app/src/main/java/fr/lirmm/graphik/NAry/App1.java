package fr.lirmm.graphik.NAry;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.commons.lang3.StringUtils;

import fr.lirmm.graphik.DEFT.gad.GADEdge;
import fr.lirmm.graphik.DEFT.gad.Derivation;
import fr.lirmm.graphik.DEFT.core.DefeasibleKB;

import fr.lirmm.graphik.NAry.ArgumentationFramework.StructuredArgument;
import fr.lirmm.graphik.NAry.ArgumentationFramework.Attack;
import fr.lirmm.graphik.NAry.Query;

import fr.lirmm.graphik.graal.api.backward_chaining.QueryRewriter;
import fr.lirmm.graphik.graal.api.core.Atom;
import fr.lirmm.graphik.graal.api.core.AtomSet;
import fr.lirmm.graphik.graal.api.core.AtomSetException;
import fr.lirmm.graphik.graal.api.core.ConjunctiveQuery;
import fr.lirmm.graphik.graal.api.core.InMemoryAtomSet;
import fr.lirmm.graphik.graal.api.core.Predicate;
import fr.lirmm.graphik.graal.api.core.Rule;
import fr.lirmm.graphik.graal.api.core.RuleSet;
import fr.lirmm.graphik.graal.api.core.RulesCompilation;
import fr.lirmm.graphik.graal.api.core.Substitution;
import fr.lirmm.graphik.graal.api.core.Term;

import fr.lirmm.graphik.graal.api.forward_chaining.Chase;
import fr.lirmm.graphik.graal.api.forward_chaining.ChaseException;
import fr.lirmm.graphik.graal.api.forward_chaining.RuleApplicationException;

import fr.lirmm.graphik.graal.api.homomorphism.Homomorphism;
import fr.lirmm.graphik.graal.api.homomorphism.HomomorphismException;
import fr.lirmm.graphik.graal.api.homomorphism.HomomorphismFactoryException;

import fr.lirmm.graphik.graal.backward_chaining.pure.AbstractRewritingOperator;
import fr.lirmm.graphik.graal.backward_chaining.pure.AggregAllRulesOperator;
import fr.lirmm.graphik.graal.backward_chaining.pure.PureRewriter;
import fr.lirmm.graphik.graal.backward_chaining.pure.RewritingOperator;

import fr.lirmm.graphik.graal.core.DefaultConjunctiveQuery;
import fr.lirmm.graphik.graal.core.atomset.LinkedListAtomSet;
import fr.lirmm.graphik.graal.core.atomset.graph.DefaultInMemoryGraphStore;
import fr.lirmm.graphik.graal.core.compilation.AbstractRulesCompilation;
import fr.lirmm.graphik.graal.core.compilation.IDCompilation;
import fr.lirmm.graphik.graal.core.factory.DefaultAtomFactory;
import fr.lirmm.graphik.graal.core.factory.DefaultRuleFactory;
import fr.lirmm.graphik.graal.core.ruleset.IndexedByHeadPredicatesRuleSet;
import fr.lirmm.graphik.graal.core.ruleset.LinkedListRuleSet;
import fr.lirmm.graphik.graal.core.term.DefaultTermFactory;
import fr.lirmm.graphik.graal.core.unifier.UnifierUtils;

import fr.lirmm.graphik.graal.forward_chaining.SccChase;
import fr.lirmm.graphik.graal.homomorphism.BacktrackHomomorphism;
import fr.lirmm.graphik.graal.homomorphism.SmartHomomorphism;
import fr.lirmm.graphik.graal.homomorphism.forward_checking.NFC2;

import fr.lirmm.graphik.graal.io.dlp.DlgpParser;
import fr.lirmm.graphik.graal.io.dlp.DlgpWriter;
import fr.lirmm.graphik.graal.io.owl.OWL2Parser;
import fr.lirmm.graphik.graal.io.owl.OWL2ParserException;

import fr.lirmm.graphik.util.Partition;
import fr.lirmm.graphik.util.profiler.AbstractProfilable;
import fr.lirmm.graphik.util.profiler.CPUTimeProfiler;
import fr.lirmm.graphik.util.profiler.Profiler;
import fr.lirmm.graphik.util.stream.CloseableIterator;
import fr.lirmm.graphik.util.stream.CloseableIteratorWithoutException;
import fr.lirmm.graphik.util.stream.IteratorException;

import javaDungAF.*;

public class App1 {
	// private static String file = "/Users/tho310/Data test/LUMP Example.dlgp";
	// private static String file = "/Users/tho310/Data test/BIO benchmark.dlgp";
	// private static String file = "/Users/tho310/Data test/TestDurum.dlgp";
	// static private String file = "C:/Users/tho310/Data test/Lum test.dlgp";
	static private String file = "C:/Users/tho310/Data test/test1.dlgp";
	private static boolean haveParameters = true;
	private static String filePath = null;

	private static InMemoryAtomSet bottomAtomset = new LinkedListAtomSet();
	private static InMemoryAtomSet equalityAtomset = new LinkedListAtomSet();
	private static ConjunctiveQuery bottomQuery = new DefaultConjunctiveQuery(bottomAtomset, Collections.emptyList());
	private static AtomSet defeasibleFacts = new LinkedListAtomSet();

	private static ArrayList<ArrayList<StructuredArgument>> extensions;
	private static ArrayList<StructuredArgument> ext;
	private static ArrayList<Attack> Attacks;
	private static ArrayList<Attack> Visited0;
	private static ArrayList<Attack> Visited;
	private static ArrayList<StructuredArgument> Reach;
	private static ArrayList<Distance> Dist;
	private static ArrayList<Distance> NewDist;
	private static Map<StructuredArgument, ArrayList<StructuredArgument>> adjacencyList;
	// public static ArrayList<StructuredArgument> Path;
	private static ArrayList<StructuredArgument> ListArgument;
	private static List<List<StructuredArgument>> tree;
	private static ArrayList<AtomSet> allMinimalConflicts;

	private static DungAF af;

	public static void main(String[] args) throws HomomorphismFactoryException, RuleApplicationException, IOException {
		long startTime = System.nanoTime();

		if ((haveParameters) && (args.length != 0)) {
			file = args[0];
		}
		/*
		 * else if (haveParameters) {
		 * System.out.println("Wrong parameters, please give a DLGP file");
		 * System.exit(0); }
		 */

		try {
			DefeasibleKB kb = new DefeasibleKB(file);
			DefeasibleKB kb1 = new DefeasibleKB(file);
			DefeasibleKB kbGenArgs = new DefeasibleKB();
			AtomSet initialFacts = new LinkedListAtomSet();
			RuleSet negativeRuleSet = new LinkedListRuleSet();
			RuleSet positiveRuleSet = new LinkedListRuleSet();
			RuleSet rules = new LinkedListRuleSet();
			RuleSet functionalruleset = new LinkedListRuleSet();
			RuleSet ruleset = new LinkedListRuleSet();
			initialFacts.addAll(kb.facts);

//			 Read all prioritized instances
//			CloseableIterator<Atom> iter1 = InitialFacts.iterator();
//			if (filePath != null) {
//				HashMap<String, Integer> preAtoms = readPreferenceAtoms(filePath, InitialFacts);
//				System.out.println(preAtoms);
//			}

			// read all rules
			negativeRuleSet = kb.negativeConstraintSet;
			System.out.println("Negative rules:" + negativeRuleSet);
			positiveRuleSet = kb.rules;
			System.out.println("Positive rules:" + positiveRuleSet);

			// get functional rules (equality-EGD)
			Iterator ck = positiveRuleSet.iterator();
			while (ck.hasNext()) {
				Rule r1 = (Rule) ck.next();
				if (r1.getHead().iterator().next().getPredicate().equals(Predicate.EQUALITY)) {
					functionalruleset.add(r1);
				} else {
					rules.add(r1);
				}

			}

			ruleset.addAll(positiveRuleSet.iterator());
			ruleset.addAll(negativeRuleSet.iterator());

			// Since quality rules can not be used for generating arguments,
			// we create a KB2 that has only TGDs, no equality and negative rules to
			// generate arguments.

			CloseableIterator<Atom> it = (CloseableIterator<Atom>) initialFacts.iterator();
			while (it.hasNext()) {
				Atom a = it.next();
				kbGenArgs.addAtom(a);
			}
			Iterator it2 = positiveRuleSet.iterator();
			while (it2.hasNext()) {
				Rule r2 = (Rule) it2.next();
				if (!r2.getHead().iterator().next().getPredicate().equals(Predicate.EQUALITY)) {
					kbGenArgs.addRule(r2);
				}
			}

			kbGenArgs.saturate();
			InMemoryAtomSet saturatedAtoms = new LinkedListAtomSet();
			saturatedAtoms.addAll(kbGenArgs.facts);
			kbGenArgs.unsaturate();

			// Generate arguments deduced from a KB
			ListArgument = generateArgs(kbGenArgs);

			// Check whether premises of arguments are consistent
			// If Yes, remove it from ListArgument, otherwise, keep it.

			AtomSet Test;
			for (int i = ListArgument.size() - 1; i >= 0; i--) {
				Test = new LinkedListAtomSet();
				for (Atom p : ((StructuredArgument) ListArgument.get(i)).getPremises()) {
					Test.add(p);
				}
				kbGenArgs.strictAtomSet = Test;
				if (RIncosistent(kbGenArgs)) {
					ListArgument.remove(i);
				}
			}

			System.out.println(".......List of arguments.......");
			for (StructuredArgument A : ListArgument) {
				System.out.println(A);
			}
			System.out.println("Number of args: " + ListArgument.size());
			long endTime = System.nanoTime();
			long duration = endTime - startTime;
			System.out.println(duration / 1000000L + " ms");

			// Compute all attackers
			// Attacks = new ArrayList();
			// kb.saturate();

			// compute attacks under equality rule
			/*
			 * if (!functionalruleset.isEmpty()) { for (StructuredArgument a : ListArgument)
			 * { ArrayList<Atom> supportsA = a.getPremises(); for (Argument b :
			 * ListArgument) { Atom conB = b.head;
			 * 
			 * // Compare the conclusion of B to the support of A ArrayList<Argument> temp =
			 * new ArrayList<Argument>(); if (checkInequality(supportsA, conB,
			 * functionalruleset) == true) { temp.add(b); }
			 * 
			 * // Check whether an argument b is in the premises of another argument // if
			 * Yes, then we donot add b to attackers of the argument a // if No, then we add
			 * b to attackers of the argument a
			 * 
			 * if (!temp.isEmpty()) { Attack add = new Attack(temp, a); if
			 * (checkAttacks(Attacks, add) == false) { Attacks.add(add); } } } } }
			 */

			/*
			 * if (!negativeRuleSet.isEmpty()) { for (Argument a : ListArgument) {
			 * ArrayList<Atom> supA = a.getPremises();
			 * 
			 * for (Argument b : ListArgument) { if (!b.equals(a)) { AtomSet u = new
			 * LinkedListAtomSet(); for (Atom atom : supA) u.add(atom); u.add(b.head);
			 * kb.facts = u; kb.saturateWithNegativeConstraint(); InMemoryAtomSet
			 * newSaturatedAtoms = new LinkedListAtomSet();
			 * newSaturatedAtoms.addAll(kb.facts); Boolean inconsistent = RIncosistent(kb);
			 * if (inconsistent) { ArrayList<Argument> temp = new ArrayList<>();
			 * temp.add(b); Attack at = new Attack(temp, a); if (checkAttacks(Attacks, at)
			 * == false) { Attacks.add(at); } } } } } }
			 */

			/* the case of negative rules */
			/*
			 * ArrayList<AtomSet> repairs = new ArrayList<AtomSet>(); if
			 * (!negativeRuleSet.isEmpty()) { // Step1: Convert LinkedListAtomSet to
			 * ArrayList
			 * 
			 * // Compute a set of repairs.
			 * 
			 * repairs = ComputeAllRepairs(kb1); ArrayList<ArrayList<String>> repairString =
			 * new ArrayList(); Iterator<AtomSet> s = repairs.iterator(); ArrayList subList
			 * = new ArrayList(); ArrayList<String> tempt = new ArrayList(); while
			 * (s.hasNext()) { AtomSet pr = s.next(); tempt =
			 * AtomSetIntoArrayWithoutArity(pr); repairString.add(tempt); }
			 * 
			 * // Convert ArrayList<ArrayList<String>> (repairString) to //
			 * ArrayList<ArrayList<Atom>> (repairsAtom) ArrayList repairsAtom = new
			 * ArrayList(); Iterator localIterator3; Iterator localIterator2 =
			 * repairString.iterator(); CloseableIterator T; for (int i = 0; i <
			 * repairString.size(); i++) { ArrayList R = (ArrayList) repairString.get(i);
			 * localIterator3 = R.iterator(); while (localIterator3.hasNext()) { String r =
			 * (String) localIterator3.next(); repairsAtom.add(new ArrayList()); T =
			 * saturatedAtoms.iterator(); while (T.hasNext()) { Atom t = (Atom) T.next(); if
			 * (AtomWithoutArity(t).equals(r)) { ((ArrayList)
			 * repairsAtom.get(repairsAtom.size() - 1)).add(t); } } } }
			 * 
			 * System.out.println("repair: " + repairs);
			 * 
			 * // Step2: Compute a set of arguments apprearing in the repairs.
			 * 
			 * HashMap<AtomSet, ArrayList<Argument>> Arg = new HashMap<AtomSet,
			 * ArrayList<Argument>>(); Iterator<AtomSet> localIterator4 =
			 * repairs.iterator(); while (localIterator4.hasNext()) { AtomSet r =
			 * localIterator4.next(); Arg.put(r, new ArrayList<Argument>());
			 * Iterator<Argument> T1 = ListArgument.iterator(); while (T1.hasNext()) {
			 * Argument Ar = (Argument) T1.next(); ArrayList<Atom> atom1 = Ar.getPremises();
			 * Boolean checkAtom = true; for (int k = 0; k < atom1.size(); k++) { if
			 * (!r.contains(atom1.get(k))) { checkAtom = false; } } if (checkAtom == true) {
			 * Arg.get(r).add(Ar); } } }
			 * 
			 * // ArrayList Attacks = new ArrayList(); for (AtomSet As : repairs) {
			 * ArrayList<Argument> NotInArg = new ArrayList<Argument>(); // Step 4: compute
			 * a set of arguments that are not in Arg, and them to NotInArg.
			 * ArrayList<Argument> arrayArg = Arg.get(As); for (Argument a : ListArgument) {
			 * if (!arrayArg.contains(a)) { NotInArg.add(a); } }
			 * 
			 * // Step 5: For each argument that is NotInArg, compute attack relation of //
			 * arguments for (Argument temp : NotInArg) { Argument aInTemp = temp; ArrayList
			 * newS = new ArrayList(); newS.add(new ArrayList()); AllSubset(newS, arrayArg);
			 * // get(r) newS.remove(0); for (int i = newS.size() - 1; i >= 0; i--) {
			 * ArrayList Concs = new ArrayList(); for (Object b1 : (ArrayList) newS.get(i))
			 * { Argument b = (Argument) b1; Concs.add(b.head); } // check whether two
			 * arguments are conflict (inconsistent)
			 * 
			 * int iter = 0; boolean inconsistent = false; while ((!inconsistent) && (iter <
			 * aInTemp.getPremises().size())) { AtomSet u = new LinkedListAtomSet(); for
			 * (Object c1 : Concs) { Atom c = (Atom) c1; u.add(c); } u.add((Atom)
			 * aInTemp.getPremises().get(iter));
			 * 
			 * kb.strictAtomSet = u; kb.saturate(); InMemoryAtomSet newSaturatedAtoms = new
			 * LinkedListAtomSet(); newSaturatedAtoms.addAll(kb.facts); inconsistent =
			 * IsInconsistent(newSaturatedAtoms, ruleset); iter++; } if (!inconsistent) {
			 * newS.remove(i); }
			 * 
			 * }
			 * 
			 * ArrayList truth = new ArrayList(); for (int i = 0; i < newS.size(); i++)
			 * truth.add(Boolean.valueOf(true)); for (int i = newS.size() - 1; i >= 1; i--)
			 * { for (int j = i - 1; j >= 0; j--) { if (((ArrayList)
			 * newS.get(i)).containsAll((Collection) newS.get(j))) { truth.set(i,
			 * Boolean.valueOf(false)); } else if (((ArrayList)
			 * newS.get(j)).containsAll((Collection) newS.get(i))) { truth.set(j,
			 * Boolean.valueOf(false)); } } }
			 * 
			 * for (int j = newS.size() - 1; j >= 0; j--) { if (!((Boolean)
			 * truth.get(j)).booleanValue()) { newS.remove(j); } }
			 * 
			 * for (int k = 0; k < newS.size(); k++) { Attack toAdd = new Attack((ArrayList)
			 * newS.get(k), aInTemp); // if (!Attacks.contains(toAdd)) { //
			 * Attacks.add(toAdd); // } // check whether an attack is in the set of attacks
			 * if (checkAttacks(Attacks, toAdd) == false) { Attacks.add(toAdd); } }
			 * 
			 * } } }
			 */

			/*
			 * System.out.println("..............."); Iterator At = Attacks.iterator();
			 * while (At.hasNext()) { Attack a = (Attack) ((Iterator) At).next();
			 * System.out.println(a); } System.out.println("There are " +
			 * ListArgument.size() + " arguments and " + Attacks.size() + " attacks.");
			 * 
			 * ArrayList<Attack> tempAtt = new ArrayList<Attack>(Attacks);
			 */
			/*
			 * Compute attacks with preferences if (filePath != null) { Integer result =
			 * null; CloseableIterator<Atom> it1 = InitialFacts.iterator();
			 * while(it1.hasNext()) { Atom atom = it1.next(); String aString =
			 * AtomWithoutArity(atom); for (Map.Entry<String, Integer> atom1 :
			 * preAtoms.entrySet()) { if (aString.compareTo(atom1.getKey()) == 0) { result =
			 * atom1.getValue(); } } }
			 */

			// compute attacks with considering preferences
			// ArrayList<Attack> tempAtt = new ArrayList<Attack>(Attacks);

			/*
			 * ArrayList<Attack> tempAtt = new ArrayList<Attack>(); for (int i = 0; i <
			 * Attacks.size(); i++) { Attack att = Attacks.get(i); ArrayList<Argument>
			 * sourceAtt = att.source; System.out.println(sourceAtt); ArrayList<Atom>
			 * targetAtom = att.target.getPremises(); System.out.println(targetAtom); for
			 * (int j = 0; j < sourceAtt.size(); j++) { ArrayList<Atom> sourceAtom =
			 * sourceAtt.get(j).getPremises(); if (isGPcomparing(sourceAtom, targetAtom,
			 * preAtoms) == true ) { tempAtt.add(att); } } } }
			 */

			// compute stable/ preferred extensions

			/*
			 * HashSet<String> argString = new HashSet<String>(); af = new DungAF(); // read
			 * arguments from ListArgument (ArrayList<Argument>) to HashSet<String> for
			 * (Argument a : ListArgument) { String aString = "A" + a.myID;
			 * af.addArgs(aString); } argString = af.getArgs();
			 * 
			 * // read attacks from Attacks (ArrayList<Attack>) to HashSet<String>
			 * 
			 * HashSet<String[]> atts = new HashSet<>(); for (int i = 0; i < tempAtt.size();
			 * i++) { Attack at = (Attack) tempAtt.get(i); String target = "A" +
			 * at.target.myID; String source = new String(); for (Argument argS : at.source)
			 * { source = "A" + argS.myID; } af.addAtts(new String[][] { { source, target }
			 * }); } atts = af.getAtts();
			 * 
			 * // Compute preferred sematics HashSet<HashSet<String>> preferredExts = new
			 * HashSet<HashSet<String>>(); preferredExts = af.getPreferredExts();
			 * System.out.println("preferred extensions: " + preferredExts);
			 * 
			 * // Compute grounded sematics HashSet<String> groundedExts = new
			 * HashSet<String>(); groundedExts = af.getGroundedExt();
			 * System.out.println("Grounded extensions: " + groundedExts);
			 * 
			 * // convert grounded extentions from HashSet<String> to ArrayList<Argument>
			 * 
			 * ArrayList<Argument> grd = new ArrayList<Argument>();
			 * 
			 * for (String s : groundedExts) { for (Argument arg : ListArgument) { String id
			 * = "A" + arg.myID; if (s.contains(id)) { grd.add(arg); } } }
			 * 
			 * // convert extensions from HashSet<HashSet<String>> to
			 * ArrayList<ArrayList<Argument>>
			 * 
			 * 
			 * extensions = new ArrayList<ArrayList<Argument>>(); for (HashSet<String>
			 * extString : preferredExts) { ext = new ArrayList<Argument>(); for (Argument
			 * arg : ListArgument) { String argID = "A" + arg.myID; if
			 * (extString.contains(argID)) { ext.add(arg); }
			 * 
			 * } extensions.add(ext); }
			 */

			/* Get union of extensions for skeptical semantics */
			/*
			 * ArrayList<Argument> preferredScepticalExt = new ArrayList<Argument>();
			 * preferredScepticalExt = getPreferredScepticalExt(extensions);
			 * System.out.println("Sceptical extensions: " + preferredScepticalExt);
			 */

			/* Get answers from a CQ query or an Instance query */

			// ConjunctiveQuery query = DlgpParser.parseQuery("? :- professor(ann).");
			// ConjunctiveQuery query = DlgpParser.parseQuery("? :- phD(ann),
			// teach(ann,X).");
			// ConjunctiveQuery query = DlgpParser.parseQuery("?(X) :- teach(ann,X).");
			// ConjunctiveQuery query = DlgpParser.parseQuery("? :- advisor(ann,bob).");
			// ConjunctiveQuery query = DlgpParser.parseQuery("? :-
			// associateProfessor(ann).");
			// String queryString = "? :- postdoc(ann).";
			/*
			 * String queryString = "?(X) :-" + " professor(X).";
			 * 
			 * ConjunctiveQuery query = DlgpParser.parseQuery(queryString);
			 * 
			 * ArrayList<AtomSet> ans = Query.getAnswers(query, positiveRuleSet,
			 * saturatedAtoms); System.out.println("Answers: " + ans);
			 */

			// Get a set of arguments for a given query

			/*
			 * HashMap<AtomSet, ArrayList<Argument>> argsForQuery = new HashMap<>();
			 * argsForQuery = getArgumentsForQuery(query, positiveRuleSet, saturatedAtoms,
			 * ListArgument); System.out.println("Arguments for a given query: " +
			 * argsForQuery);
			 */

			// get attacks for an argument

			// allMinimalConflicts = FindMinIncSets.findMinimalIncSubsets(kb);

			// System.out.println("All minimal conflicts: " + allMinimalConflicts);

			// check IAR semantic or Grounded extension
			/*
			 * int count = 0; if (includesArrayList(grd, argumentForQuery) == true) {
			 * System.out.println("accepted under grounded extenions"); } else { // Check
			 * credulous, skepcitcal, non-accept for argument for (Argument arg :
			 * argumentForQuery) { for (int i = 0; i < extensions.size(); i++) { if
			 * (extensions.get(i).contains(arg)) { count++; } } } if (count == 0) {
			 * System.out.println("non-accepted"); } else if ((count == extensions.size())
			 * || (count / extensions.size() == extensions.size())) {
			 * System.out.println("sceptical"); } else System.out.println("Creduluous"); }
			 * 
			 * System.out.println();
			 */

			// Proceduce ReReach (A, A', n, S)
			// Reach = new ArrayList<Argument>();

			// Visited0 = new ArrayList<Attack>();
			// Visited = new ArrayList<Attack>();

			/*
			 * Dist = new ArrayList<Distance>(); for (int i = 0; i < ListArgument.size();
			 * i++) { Argument a = ListArgument.get(i); // Reach.add(a); Dist.add(new
			 * Distance(a, a, 0)); for (int j = 0; j < ListArgument.size(); j++) { if (j !=
			 * i) { Argument b = ListArgument.get(j); Dist.add(new Distance(a, b, 0)); } } }
			 * 
			 * if (includesArrayList(grd, argumentForQuery) == true) { for (Argument a :
			 * argumentForQuery) { Visited = new ArrayList<Attack>(); NewDist = new
			 * ArrayList<Distance>(); Reach = new ArrayList<Argument>(); ReReach(a, a, 0,
			 * null, Attacks); ArrayList<Argument> reachOdd = new ArrayList<>();
			 * ArrayList<Argument> reachEven = new ArrayList<>(); reachOdd = getReachOdd(a,
			 * NewDist); reachEven = getReachEven(a, NewDist);
			 * 
			 * // print paths from A to B
			 * 
			 * Graph graph = new Graph(); // addEdge to graph for (int i = 0; i <
			 * tempAtt.size(); i++) { Attack at = (Attack) tempAtt.get(i);
			 * graph.addEdge(at.target, at.source); }
			 * 
			 * Argument start = a; for (Argument b : grd) { Argument end = b; if
			 * (!start.equals(end)) { graph.printAllPaths(start, end); } } }
			 * 
			 * // there is no attacks }
			 */

			/*
			 * if (count == 0) {
			 * 
			 * for (Argument a : argumentForQuery) { Visited = new ArrayList<Attack>();
			 * NewDist = new ArrayList<Distance>(); Reach = new ArrayList<Argument>();
			 * ReReach(a, a, 0, null, Attacks);
			 * 
			 * ArrayList<Argument> reachOdd = new ArrayList<>(); ArrayList<Argument>
			 * reachEven = new ArrayList<>(); reachOdd = getReachOdd(a, NewDist);
			 * 
			 * // Compute NotDef for an argument wrt extensions
			 * ArrayList<ArrayList<Argument>> NotDefOfA = computeNotDefBy(reachOdd,
			 * extensions, NewDist); // merge all extensions to one Set<Argument> set = new
			 * HashSet<Argument>(); for (int i = 0; i < NotDefOfA.size(); i++) {
			 * set.addAll(NotDefOfA.get(i)); } ArrayList<Argument> combinedList = new
			 * ArrayList<>(set); System.out.println(combinedList);
			 * 
			 * // print paths from A to B Graph graph = new Graph(); // addEdge to graph for
			 * (int i = 0; i < tempAtt.size(); i++) { Attack at = (Attack) tempAtt.get(i);
			 * graph.addEdge(at.target, at.source); } Argument start = a;
			 * System.out.println("path: "); tree = new ArrayList<>(); List<List<Argument>>
			 * paths = new ArrayList<>(); for (Argument b : combinedList) { Argument end =
			 * b; paths = graph.printAllPathsEven(start, end); for (List<Argument> path :
			 * paths) { tree.add(path); } } } for (List<Argument> p : tree) {
			 * System.out.println(p); }
			 * 
			 * }
			 */
			/*
			 * else if ((count == extensions.size()) || (count / extensions.size() ==
			 * extensions.size())) { for (Argument a : argumentForQuery) { Visited = new
			 * ArrayList<Attack>(); NewDist = new ArrayList<Distance>(); Reach = new
			 * ArrayList<Argument>(); ReReach(a, a, 0, null, Attacks); ArrayList<Argument>
			 * reachOdd = new ArrayList<>(); ArrayList<Argument> reachEven = new
			 * ArrayList<>(); reachOdd = getReachOdd(a, NewDist); //
			 * System.out.println("Reach odd: " + reachOdd); reachEven = getReachEven(a,
			 * NewDist); ArrayList<Argument> DefBy = reachEven;
			 * 
			 * // compute a set of extension for an argument and merge them into one set.
			 * Set<Argument> merge = new HashSet<Argument>(); for (int i = 0; i <
			 * extensions.size(); i++) { ArrayList<Argument> subDef = intersection(DefBy,
			 * extensions.get(i)); merge.addAll(subDef); } ArrayList<Argument> DefByExt =
			 * new ArrayList<>(merge); // System.out.println("DefBy: " + DefByExt);
			 * 
			 * // print paths from A to B
			 * 
			 * Graph graph = new Graph(); // addEdge to graph for (int i = 0; i <
			 * tempAtt.size(); i++) { Attack at = (Attack) tempAtt.get(i);
			 * graph.addEdge(at.target, at.source); }
			 * 
			 * Argument start = a; List<List<Argument>> allPaths = new ArrayList<>(); tree =
			 * new ArrayList<>(); for (Argument b : DefByExt) {
			 * 
			 * Argument end = b; if (!start.equals(end)) { allPaths =
			 * graph.printAllPathsOdd(start, end); // allPaths = graph.printAllPaths(start,
			 * end); for (List<Argument> path : allPaths) { tree.add(path); } }
			 * 
			 * }
			 * 
			 * for (List<Argument> t : tree) { System.out.println(t.toString());
			 * printDialogue(t); } }
			 * 
			 * }
			 */
			// credulous
			/*
			 * else { for (Argument a : argumentForQuery) { Visited = new
			 * ArrayList<Attack>(); NewDist = new ArrayList<Distance>(); Reach = new
			 * ArrayList<Argument>(); ReReach(a, a, 0, null, Attacks);
			 * 
			 * ArrayList<Argument> reachOdd = new ArrayList<>(); ArrayList<Argument>
			 * reachEven = new ArrayList<>(); reachOdd = getReachOdd(a, NewDist); reachEven
			 * = getReachEven(a, NewDist); ArrayList<Argument> DefBy = reachEven; // Compute
			 * Def for an argument wrt extensions
			 * 
			 * Set<Argument> merge = new HashSet<Argument>(); for (int i = 0; i <
			 * extensions.size(); i++) { ArrayList<Argument> subDef = intersection(DefBy,
			 * extensions.get(i)); merge.addAll(subDef); } ArrayList<Argument> DefByExt =
			 * new ArrayList<>(merge);
			 * 
			 * ArrayList<ArrayList<Argument>> NotDefOfA = computeNotDefBy(reachOdd,
			 * extensions, NewDist); Set<Argument> set = new HashSet<Argument>(); for (int i
			 * = 0; i < NotDefOfA.size(); i++) { set.addAll(NotDefOfA.get(i)); }
			 * ArrayList<Argument> combinedList = new ArrayList<>(set);
			 * 
			 * Graph graph = new Graph(); // addEdge to graph for (int i = 0; i <
			 * tempAtt.size(); i++) { Attack at = (Attack) tempAtt.get(i);
			 * graph.addEdge(at.target, at.source); }
			 * 
			 * Argument start = a; tree = new ArrayList<>(); for (Argument b : combinedList)
			 * { Argument end1 = b;
			 * 
			 * List<List<Argument>> paths = graph.printAllPathsEven(start, end1); for
			 * (List<Argument> p : paths) { tree.add(p); } }
			 * 
			 * for (Argument b : DefByExt) { Argument end = b; List<List<Argument>> paths1 =
			 * graph.printAllPaths(start, end); for (List<Argument> p : paths1) {
			 * tree.add(p); } }
			 * 
			 * for (List<Argument> t : tree) { System.out.println(t); printDialogue(t); } }
			 * 
			 * }
			 * 
			 * }
			 */
		}

		catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IteratorException e) {
			e.printStackTrace();
		} catch (AtomSetException e) {
			e.printStackTrace();
		} catch (ChaseException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
			// } catch (HomomorphismException e) {
			// e.printStackTrace();
		} // catch (OWL2ParserException e) {
			// e.printStackTrace();
			// }

		long endTime = System.nanoTime();
		long duration = endTime - startTime;
		System.out.println(duration / 1000000L + " ms");
	}

	/*
	 * Generate a set of arguments from KB, which includes steps: 1)
	 * cartesianProduct for computing all sets 2) allSubsets for computing all
	 * subsets of arguments 3) recurSiveArgs for recursively computing the structure
	 * of arguments 4) generateArgs. This function to generate all arguments
	 */

	// 1) compute all sets of atoms
	protected static <T> List<List<T>> cartesianProduct(List<List<T>> lists) {
		List resultLists = new ArrayList();
		if (lists.size() == 0) {
			resultLists.add(new ArrayList());
			return resultLists;
		}
		List firstList = (List) lists.get(0);
		List remainingLists = cartesianProduct(lists.subList(1, lists.size()));
		Iterator localIterator1 = firstList.iterator();
		while (localIterator1.hasNext()) {
			Object condition = (Object) localIterator1.next();
			Iterator localIterator2 = remainingLists.iterator();

			while (localIterator2.hasNext()) {
				List remainingList = (List) localIterator2.next();
				ArrayList resultList = new ArrayList();
				resultList.add(condition);
				resultList.addAll(remainingList);
				resultLists.add(resultList);
			}
		}
		return resultLists;
	}

	// 2) compute all set of arguments

	public static void AllSubset(ArrayList<ArrayList<StructuredArgument>> S, ArrayList<StructuredArgument> F)
			throws AtomSetException, ChaseException, HomomorphismException {
		ArrayList F2 = new ArrayList();
		F2.addAll(F);

		if (!F2.isEmpty()) {
			StructuredArgument a = (StructuredArgument) F2.get(0);

			ArrayList Temp = new ArrayList();
			for (ArrayList s : S) {
				ArrayList sTemp = new ArrayList();
				sTemp.addAll(s);
				sTemp.add(a);
				Temp.add(sTemp);
			}

			// for (ArrayList s : Temp)
			for (Object s1 : Temp) {
				ArrayList s = (ArrayList) s1;
				S.add(s);
			}
			F2.remove(0);

			AllSubset(S, F2);
		}
	}

	// 3) compute recursively arguments deduced from a KBs

	public static void recurSiveArgs(Atom a, HashMap<Atom, ArrayList<StructuredArgument>> dico, DefeasibleKB kb) {
		try {
			Iterator localIterator2;
			Iterator localIterator1 = kb.gad.getDerivations(a).iterator();
			while (localIterator1.hasNext()) {
				Derivation d = (Derivation) localIterator1.next();
				localIterator2 = d.iterator();
				while (localIterator2.hasNext()) {
					GADEdge ge = (GADEdge) localIterator2.next();

					if ((ge.getSources() == null) && (ge.getTarget().equals(a))) // this is a fact
					{
						if (dico.get(a) == null) {
							dico.put(a, new ArrayList<StructuredArgument>());
						}
						boolean contain = false;
						for (StructuredArgument p : dico.get(a)) {
							if (((p.IsPremise = Boolean.valueOf(true)).booleanValue()) && (p.head.equals(a))) {
								contain = true;
							}

						}

						if (!contain)
							((ArrayList) dico.get(a))
									.add(new StructuredArgument(new ArrayList(), a, Boolean.valueOf(true)));
					}

					else if (ge.getTarget().equals(a)) {
						ArrayList<Atom> Source = new ArrayList<>();

						if (ge.getSources() != null) {
							CloseableIterator so = ge.getSources().iterator();
							while (so.hasNext()) {
								Atom nextOne = (Atom) so.next();
								Source.add(nextOne);
								recurSiveArgs(nextOne, dico, kb);
							}

						}

						if (dico.get(a) == null) {
							dico.put(a, new ArrayList());
						}
						List T = new ArrayList();
						for (Atom m : Source) {
							T.add((List) dico.get(m));
						}
			

						for (Object p1 : cartesianProduct(T)) {
							List p = (List) p1;
							ArrayList copy = new ArrayList();
							copy.addAll(p);

							boolean contain = false;

							for (StructuredArgument z : (ArrayList<StructuredArgument>) dico.get(a)) {
								if ((z.body.containsAll(copy)) && (copy.containsAll(z.body))) {
									contain = true;
								}
							}

							if (!contain) {
								((ArrayList) dico.get(a)).add(new StructuredArgument(copy, a, Boolean.valueOf(false)));
							}
						}
					}
				}
			}
		} catch (IteratorException e) {
			e.printStackTrace();
		}
	}

	// 4) compute all arguments from a KBs

	public static ArrayList<StructuredArgument> generateArgs(DefeasibleKB kb) {
		ArrayList<StructuredArgument> result = new ArrayList<>();
		HashMap dictionnary = new HashMap();

		for (Atom a : kb.gad.getVertices()) {
			recurSiveArgs(a, dictionnary, kb);
		}

		// for (Atom a : dictionnary.keySet()) {
		for (Object a1 : dictionnary.keySet()) {
			Atom a = (Atom) a1;
			result.addAll((Collection) dictionnary.get(a));
		}

		return result;
	}

	// This function is used to remove the premises of argument that are
	// inconsistent
	public static boolean RIncosistent(DefeasibleKB kb) {
		boolean result = false;
		try {
			for (Predicate s : kb.facts.getPredicates())
				if (s.equals(Predicate.BOTTOM)) {
					result = true;
				}
		} catch (AtomSetException e) {
			e.printStackTrace();
		}
		return result;
	}

	public static ArrayList<AtomSet> ComputeAllRepairs(DefeasibleKB kb)
			throws AtomSetException, ChaseException, HomomorphismException, OWL2ParserException, IOException {
		InMemoryAtomSet atomset = new LinkedListAtomSet();
		RuleSet ruleset = new LinkedListRuleSet();
		RuleSet negativeRuleSet = new LinkedListRuleSet();
		RuleSet positiveRuleSet = new LinkedListRuleSet();
		RuleSet rules = new LinkedListRuleSet();
		RuleSet functionalRuleSet = new LinkedListRuleSet();
		ArrayList<AtomSet> S = new ArrayList<AtomSet>();
		ArrayList<AtomSet> repair = new ArrayList<AtomSet>();

		AtomSet InitialFacts = new LinkedListAtomSet();
		InitialFacts.addAll(kb.facts);
		atomset.addAll(kb.facts);

		kb.saturateWithNegativeConstraint();

		InMemoryAtomSet saturatedAtoms = new LinkedListAtomSet();
		saturatedAtoms.addAll(kb.facts);

		negativeRuleSet = kb.negativeConstraintSet;
		positiveRuleSet = kb.rules;

		Iterator it = positiveRuleSet.iterator();

		/* add equality rules to negative rules */

		while (it.hasNext()) {
			Rule r = (Rule) it.next();
			if (r.getHead().iterator().next().getPredicate().equals(Predicate.EQUALITY)) {
				negativeRuleSet.add(r);
			} else {
				rules.add(r);
			}
		}

		ruleset.addAll(positiveRuleSet.iterator());
		ruleset.addAll(negativeRuleSet.iterator());

		// @SuppressWarnings("unchecked")
		// Chase mychase = new SccChase(ruleset.iterator(), saturatedAtomS);
		// mychase.execute();

		ArrayList IsRepair = null;
		int numberOfRepairs = 0;
		ArrayList<AtomSet> setOfRepairs = new ArrayList<AtomSet>();
		if (!negativeRuleSet.iterator().hasNext()) {
			S.add(atomset);
			numberOfRepairs++;
			IsRepair = new ArrayList();
			IsRepair.add(Boolean.valueOf(true));
		} else {
			S.add(new LinkedListAtomSet());
			AllConsistentSubset(S, atomset, ruleset);
			IsRepair = new ArrayList();
			IsRepair.add(Boolean.valueOf(false));
			for (int i = 1; i < S.size(); i++) {
				IsRepair.add(Boolean.valueOf(true));
			}

			for (int k = 0; k < S.size() - 1; k++) {
				for (int l = k + 1; l < S.size(); l++) {
					AtomSet a = (AtomSet) S.get(k);
					AtomSet b = (AtomSet) S.get(l);

					Boolean bIncluded = containsAll(a, b);
					Boolean aIncluded = containsAll(b, a);
					if (aIncluded.booleanValue()) {
						IsRepair.set(k, Boolean.valueOf(false));
					} else if (bIncluded.booleanValue())
						IsRepair.set(l, Boolean.valueOf(false));
				}
			}

			for (int i = 0; i < S.size(); i++) {
				if (((Boolean) IsRepair.get(i)).booleanValue())
					numberOfRepairs++;

			}
		}
		for (int i = 0; i < S.size(); i++) {
			if (((Boolean) IsRepair.get(i)).booleanValue()) {
				setOfRepairs.add(S.get(i));
			}
		}
		return setOfRepairs;

	}

	private static void AllConsistentSubset(ArrayList<AtomSet> S, InMemoryAtomSet F, RuleSet ruleset)
			throws IteratorException, AtomSetException, ChaseException, HomomorphismException {

		// InMemoryAtomSet bottomAtomset = new LinkedListAtomSet();
		bottomAtomset.add(DefaultAtomFactory.instance().getBottom());
		ConjunctiveQuery bottomQuery = new DefaultConjunctiveQuery(bottomAtomset, Collections.emptyList());

		// Atom bot = DefaultAtomFactory.instance().getBottom();
		if (F.iterator().hasNext()) {
			CloseableIterator iterat = (CloseableIterator) F.iterator();
			Atom a = (Atom) iterat.next();

			ArrayList Temp = new ArrayList();
			for (AtomSet s : S) {
				InMemoryAtomSet sTemp = new LinkedListAtomSet();
				InMemoryAtomSet sTemp1 = new LinkedListAtomSet();
				sTemp.addAll(s);
				sTemp.add(a);
				sTemp1.addAll(s);
				sTemp1.add(a);

				// Chase chase = new SccChase(ruleset.iterator(),sTemp1);
				// chase.execute();
				Chase mychase = new SccChase(ruleset.iterator(), sTemp1);
				mychase.execute();

				CloseableIterator<Substitution> results = SmartHomomorphism.instance().execute(bottomQuery, sTemp1);

				/* sTemp must be an atom set */

				if (!results.hasNext()) {
					Temp.add(sTemp1);
				}

			}

			for (Object s1 : Temp) {
				AtomSet s = (AtomSet) s1;
				S.add(s);
			}
			InMemoryAtomSet newF = new LinkedListAtomSet();
			while (iterat.hasNext())
				newF.add((Atom) iterat.next());
			AllConsistentSubset(S, newF, ruleset);
		}
	}

	public static ArrayList<String> AtomSetIntoArrayWithoutArity(AtomSet a) throws IteratorException {
		ArrayList result = new ArrayList();
		CloseableIterator iter = a.iterator();
		while (iter.hasNext())
			result.add(AtomWithoutArity((Atom) iter.next()));
		return result;
	}

	public static ArrayList<String> AtomSetIntoArrayWithoutArity1(ArrayList<Atom> a) {
		ArrayList result = new ArrayList();
		for (Atom at : a) {
			result.add(AtomWithoutArity(at));
		}
		return result;
	}

	public static String AtomWithoutArity(Atom a) {
		String result = "";
		result = result + a.getPredicate().getIdentifier();
		result = result + "(";
		for (int i = 0; i < a.getTerms().size() - 1; i++) {
			result = result + a.getTerm(i) + ",";
		}
		if (!a.getTerms().isEmpty())
			result = result + a.getTerm(a.getTerms().size() - 1);
		result = result + ")";
		return result;
	}

	public static boolean containsAll(AtomSet A, AtomSet B) throws IteratorException, AtomSetException {
		boolean result = true;

		CloseableIterator ite = B.iterator();
		while (ite.hasNext()) {
			if (!A.contains((Atom) ite.next())) {
				result = false;
			}
		}

		return result;
	}

	public static boolean IsInconsistent(AtomSet s, RuleSet ruleset)
			throws HomomorphismException, ChaseException, AtomSetException, IteratorException {
		InMemoryAtomSet sTemp = new LinkedListAtomSet();
		sTemp.addAll(s);

		Chase mychase = new SccChase(ruleset.iterator(), sTemp);
		mychase.execute();

		CloseableIterator<Substitution> results = SmartHomomorphism.instance().execute(bottomQuery, sTemp);

		if (!results.hasNext()) {
			return false;
		}

		return true;
	}

	// Get arguments for a given query from a given list of arguments.

	// 1) Get arguments for an atom
	public static ArrayList<StructuredArgument> getArgumentsForAtom(Atom atom,
			ArrayList<StructuredArgument> listOfArgs) {
		ArrayList<StructuredArgument> arguments = new ArrayList();
		for (StructuredArgument a : listOfArgs) {
			if (a.head.equals(atom))
				arguments.add(a);

		}
		return arguments;
	}

	// 2) Get arguments for an AtomSet (conjunctive atoms)
	public static ArrayList<ArrayList<StructuredArgument>> getArgsForAtomSet(AtomSet set,
			ArrayList<StructuredArgument> listOfArgs) throws IteratorException {
		ArrayList<ArrayList<StructuredArgument>> result = new ArrayList<>();
		Map<String, StructuredArgument> argMap = new HashMap<>();
		// Preprocess listOfArgs into a HashMap
		for (StructuredArgument arg : listOfArgs) {
			String key = arg.head.getPredicate() + ":" + arg.head.getConstants().toString();
			argMap.put(key, arg);
		}

		CloseableIterator<Atom> it = set.iterator();
		while (it.hasNext()) {
			Atom a = it.next();
			String key = a.getPredicate() + ":" + a.getConstants().toString();

			StructuredArgument arg = argMap.get(key);
			//if (arg != null && arg.head.equals(a)) {
			if (arg != null || (arg.head.equals(a) || 
				    (arg.head.getPredicate().equals(a.getPredicate()) && 
				     arg.head.getConstants().equals(a.getConstants())))) {
				result.add(getArgumentsForAtom(a, listOfArgs));
			}
		}
		return result;
	}

	// Get arguments for a given query that could be IQs or CQs
	
	public static HashMap<AtomSet, ArrayList<StructuredArgument>> getArgumentsForQuery(
	        ConjunctiveQuery query,
	        RuleSet positiveRuleSet,
	        InMemoryAtomSet saturatedAtoms,
	        ArrayList<StructuredArgument> listOfArgs
	) throws IteratorException, HomomorphismException {
	    // Initialize the result map to store AtomSet and corresponding argument groups
	    HashMap<AtomSet, ArrayList<StructuredArgument>> result = new HashMap<>();

	    // Retrieve all answers for the query using the provided rule set and saturated atoms
	    ArrayList<AtomSet> answers = Query.getAnswers(query, positiveRuleSet, saturatedAtoms);

	    // Iterate through each AtomSet in the answers
	    for (AtomSet atomSet : answers) {
	        // Retrieve argument groups for the current AtomSet
	        ArrayList<ArrayList<StructuredArgument>> argGroupsForAtomSet = getArgsForAtomSet(atomSet, listOfArgs);

	        // Add each argument group to the result map, associated with the current AtomSet
	        for (ArrayList<StructuredArgument> group : argGroupsForAtomSet) {
	            result.put(atomSet, group);
	        }
	    }

	    return result;
	}

	/*
	 * Check equality rules
	 */

	public static boolean equalityCompare(ArrayList<Atom> supportsA, Atom conB, RuleSet functionRules) {

		Set<Predicate> preA = new HashSet<Predicate>();
		for (int i = 0; i < supportsA.size(); i++) {
			preA.add(supportsA.get(i).getPredicate());

		}
		for (Rule r : functionRules) {
			Set<Predicate> preR = r.getBody().getPredicates();
			for (int j = 0; j < supportsA.size(); j++) {
				Atom ele = supportsA.get(j);
				if ((preR.contains(ele.getPredicate())) & (preR.contains(conB.getPredicate()))) {

					if ((ele.getTerm(0).equals(conB.getTerm(0))) & (!ele.getTerm(1).equals(conB.getTerm(1)))) {
						return true;

					}
					// only for Biogaphycal Domain
					String str1 = ele.getTerm(0).toString();
					String str2 = conB.getTerm(0).toString();
					if ((str1.substring(0, 18).equals(str2.substring(0, 18)))
							& (!ele.getTerm(1).equals(conB.getTerm(1)))) {
						return true;
					}
				}
			}

		}
		return false;

	}

	/* Get union of extensions for sceptical semantics */

	public static ArrayList<StructuredArgument> getPreferredScepticalExt(
			ArrayList<ArrayList<StructuredArgument>> preferredExts) {
		ArrayList<StructuredArgument> preferredScepticalExt = new ArrayList<StructuredArgument>();

		if (preferredScepticalExt.isEmpty()) {
			preferredScepticalExt = new ArrayList<StructuredArgument>(preferredExts.iterator().next()); // initialize
			// preferredScepticalExt
			// to a random
			// preferredExt;

			for (ArrayList<StructuredArgument> nextExt : preferredExts) {
				preferredScepticalExt.retainAll(nextExt);
			} // remove everything which isn't in every preferred extension;
		}

		return new ArrayList<StructuredArgument>(preferredScepticalExt);
	}

	/* check whether an argument is created from assertion without applying rules */

	public static boolean checkAtomArg(ArrayList<StructuredArgument> A) {
		for (int i = 0; i < A.size(); i++) {
			StructuredArgument a = A.get(i);
			if (a.getPremises().equals(a.head)) {
				return true;
			}
		}
		return false;
	}

	public static LinkedList getRemoves(LinkedList setOfAttackers) {
		LinkedList removes = new LinkedList();
		for (int i = 0; i < setOfAttackers.size(); i++) {
			ArrayList<StructuredArgument> A = (ArrayList<StructuredArgument>) setOfAttackers.get(i);
			ArrayList<Atom> atomA = new ArrayList<Atom>();
			ArrayList<StructuredArgument> bodyA = new ArrayList<StructuredArgument>();
			for (int m = 0; m < A.size(); m++) {
				StructuredArgument a = A.get(m);
				atomA.addAll(A.get(m).getPremises());
				bodyA.addAll(a.body);
			}

			for (int j = i + 1; j < setOfAttackers.size(); j++) {
				ArrayList<StructuredArgument> B = (ArrayList<StructuredArgument>) setOfAttackers.get(j);
				if (!A.equals(B)) {
					ArrayList<Atom> atomB = new ArrayList<Atom>();
					ArrayList<StructuredArgument> bodyB = new ArrayList<StructuredArgument>();
					for (int m = 0; m < B.size(); m++) {
						StructuredArgument b = B.get(m);
						atomB.addAll(B.get(m).getPremises());
						bodyB.addAll(b.body);
					}

					if ((bodyA.containsAll(bodyB)) && (atomA.containsAll(atomB))) {
						removes.add(setOfAttackers.get(j));
					}
					if ((bodyB.containsAll(bodyA)) && (atomB.containsAll(atomA))) {
						removes.add(setOfAttackers.get(i));
					}
				}
			}
		}
		return removes;

	}

	public static LinkedList<StructuredArgument> getAttackersFor(StructuredArgument arg, ArrayList SetOfAttacks,
			ArrayList<StructuredArgument> ListOfArguments) {

		Iterator iter = SetOfAttacks.iterator();
		LinkedList AttackersFor = new LinkedList();
		LinkedList removes = new LinkedList();
		if (SetOfAttacks.isEmpty()) {
			return null;
		}

		while (iter.hasNext()) {
			Attack at = (Attack) iter.next();
			if (at.target.equals(arg)) {
				AttackersFor.add(at.source);
			}
		}
		// remove sub-arguments
		// 1. compute a set of sub-arguments needed to remove
		// 2.

		removes = getRemoves(AttackersFor);
		LinkedList temp = AttackersFor;
		for (int i = 0; i < removes.size(); i++) {
			temp.remove(removes.get(i));
		}
		AttackersFor = temp;
		return AttackersFor;
	}

	public static LinkedList<Defeater> getDefeatersFor(StructuredArgument arg, ArrayList SetOfAttacks,
			ArrayList<StructuredArgument> ListOfArguments) throws AtomSetException, HomomorphismException,
			HomomorphismFactoryException, RuleApplicationException, ChaseException, IteratorException {
		LinkedList<Defeater> defeaters = new LinkedList<Defeater>();
		LinkedList<StructuredArgument> attackers = getAttackersFor(arg, SetOfAttacks, ListOfArguments);

		Iterator it = attackers.iterator();
		while (it.hasNext()) {
			ArrayList tempAttackers = new ArrayList();
			tempAttackers = (ArrayList) it.next();
			for (int i = 0; i < tempAttackers.size(); i++) {
				StructuredArgument attacker = (StructuredArgument) tempAttackers.get(i);
				int attackStatus = Defcompare(attacker, arg);
				if (attackStatus != 0) {
					defeaters.add(new Defeater(attacker, attackStatus));
				}
			}
		}

		return defeaters;
	}

	private static boolean checkSubArg(ArrayList parents, StructuredArgument a) {

		for (int i = 0; i < parents.size(); i++) {
			StructuredArgument b = (StructuredArgument) parents.get(i);
			if ((b.getPremises().containsAll(a.getPremises())) || (a.getPremises().containsAll(b.getPremises()))) {
				return true;
			}
		}
		return false;
	}

	private static ArrayList<ArrayList<StructuredArgument>> getExtentionsForAcceptance(StructuredArgument arg,
			ArrayList<ArrayList<StructuredArgument>> extensions) {
		ArrayList<ArrayList<StructuredArgument>> ExtforAcceptance = new ArrayList<ArrayList<StructuredArgument>>();
		for (int i = 0; i < extensions.size(); i++) {
			if (extensions.get(i).contains(arg)) {
				ExtforAcceptance.add(extensions.get(i));
			}
		}
		return ExtforAcceptance;
	}

	private static ArrayList<ArrayList<StructuredArgument>> getExtentionsForNonAcceptance(StructuredArgument arg,
			ArrayList<ArrayList<StructuredArgument>> extensions) {
		ArrayList<ArrayList<StructuredArgument>> ExtforAcceptance = new ArrayList<ArrayList<StructuredArgument>>();
		ArrayList<ArrayList<StructuredArgument>> ExtforNonAcceptance = new ArrayList<ArrayList<StructuredArgument>>();
		for (int i = 0; i < extensions.size(); i++) {
			if (!extensions.get(i).contains(arg)) {
				ExtforNonAcceptance.add(extensions.get(i));
			}
		}
		return ExtforNonAcceptance;
	}

	public static boolean isDefeasible(StructuredArgument arg) throws IteratorException {
		boolean isDefeasible = false;
		ArrayList<StructuredArgument> body = arg.body; // body is array list of arguments
		CloseableIterator<Atom> def = (CloseableIterator<Atom>) defeasibleFacts.iterator();
		while (def.hasNext()) {
			Atom at = def.next();

			if (arg.getPremises().contains(at)) {
				isDefeasible = true;
				break;
			}
		}
		return isDefeasible;

	}

	public static int Defcompare(StructuredArgument attacker, StructuredArgument attackee) throws IteratorException {

		if (isDefeasible(attackee) == false && isDefeasible(attacker) == false) {
			return 2;
		}

		if (isDefeasible(attackee) == false) {
			return 0;
		}

		// else, if the attacker is strict then it wins
		if (isDefeasible(attacker) == false) {
			return 1;
			// return 2;
		}
		// else, the attacker and attackee are both defeasible
		else {
			return 2;
			// return 1;
		}
	}

	public static ArrayList<StructuredArgument> getElementsNotInList2(ArrayList<StructuredArgument> list1,
			ArrayList<StructuredArgument> list2) {
		HashSet<StructuredArgument> set2 = new HashSet<>(list2);
		ArrayList<StructuredArgument> result = new ArrayList<>();

		for (StructuredArgument element : list1) {
			if (!set2.contains(element)) {
				result.add(element);
			}
		}

		return result;
	}

	public static int getPreference(Atom a, HashMap<String, Integer> preferenceAtoms) {
		Integer result = null;
		String aString = AtomWithoutArity(a);
		for (Map.Entry<String, Integer> atom : preferenceAtoms.entrySet()) {
			if (aString.compareTo(atom.getKey()) == 0) {
				result = atom.getValue();
			}
		}
		return result;
	}

	public static boolean isGPcomparing(ArrayList<Atom> list1, ArrayList<Atom> list2,
			HashMap<String, Integer> preferenceAtoms) {
		if (list1.isEmpty() || list2.isEmpty()) {
			return false;
		}

		int maxElementList2 = getPreference(list2.get(0), preferenceAtoms);

		for (Atom element : list2) {
			int pre1 = getPreference(element, preferenceAtoms);
			if (pre1 > maxElementList2) {
				maxElementList2 = pre1;
			}
		}

		for (Atom element : list1) {
			int pre2 = getPreference(element, preferenceAtoms);
			if (pre2 >= maxElementList2) {
				return true;
			}
		}

		return false;
	}

	public static int CheckingBooleanQuery(ConjunctiveQuery query, ArrayList<AtomSet> setOfRepairs,
			RuleSet positiveRuleSet, InMemoryAtomSet saturatedAtoms)
			throws IteratorException, AtomSetException, HomomorphismException {
		InMemoryAtomSet atomQuery = query.getAtomSet();
		// System.out.println(atomQuery);
		int count = 0;
		ArrayList<AtomSet> answers = new ArrayList<AtomSet>();
		answers = Query.getAnswersForCQ(query, positiveRuleSet, saturatedAtoms);
		Iterator<AtomSet> ck = answers.iterator();
		// CloseableIterator ck = atomQuery.iterator();
		while (ck.hasNext()) {
			Atom at = (Atom) ck.next();
			for (int i = 0; i < setOfRepairs.size(); i++) {
				if (setOfRepairs.get(i).contains(at)) {
					count++;
				}
			}
		}

		if (count == 0) {
			return 0; // non-acception
		}
		if (count == setOfRepairs.size()) {
			return 1; // sckeptical
		} else
			return 2; // credulous
	}

	public static boolean checkInequality(ArrayList<Atom> supportsA, Atom conB, RuleSet functionRules) {

		Set<Predicate> preA = new HashSet<Predicate>();
		for (int i = 0; i < supportsA.size(); i++) {
			preA.add(supportsA.get(i).getPredicate());

		}
		for (Rule r : functionRules) {
			Set<Predicate> preR = r.getBody().getPredicates();
			for (int j = 0; j < supportsA.size(); j++) {
				Atom ele = supportsA.get(j);
				if ((preR.contains(ele.getPredicate())) & (preR.contains(conB.getPredicate()))) {

					// lay List of terms va so sanh

					// if((ele.getTerm(0).equals(conB.getTerm(0))) &
					// (!ele.getTerm(2).equals(conB.getTerm(2)))) {
					// return true;
					// }

					// only for Biogaphycal Domain
					String str1 = ele.getTerm(0).toString();
					String str2 = conB.getTerm(0).toString();
					if ((str1.substring(0, 18).equals(str2.substring(0, 18)))
							& (!ele.getTerm(1).equals(conB.getTerm(1)))) {
						return true;
					}
				}
			}

		}
		return false;

	}

	public static boolean checkAttacks(ArrayList<Attack> A, Attack b) {
		boolean result = false;

		for (int i = 0; i < A.size(); i++) {
			Attack a = A.get(i);
			// if (((a.target.equals(b.target)) && (a.source.containsAll(b.source))) ||
			// ((a.target.equals(b.target) && checkSubArg(a.source, b.source) == true)) {
			// if (a.target.equals(b.target) && checkSubArg(a.source, b.source) == true) {
			if ((a.target.equals(b.target)) && (a.source.containsAll(b.source))) {
				result = true;
			}
		}
		return result;

	}

	public static ArrayList<StructuredArgument> GetRemovedElements(ArrayList setOfAttackers) {
		ArrayList removers = new ArrayList<>();
		for (int i = 0; i < setOfAttackers.size(); i++) {
			ArrayList<StructuredArgument> A = (ArrayList<StructuredArgument>) setOfAttackers.get(i);
			ArrayList<Atom> atomA = new ArrayList<Atom>();
			ArrayList<StructuredArgument> bodyA = new ArrayList<StructuredArgument>();
			for (int m = 0; m < A.size(); m++) {
				StructuredArgument a = A.get(m);
				atomA.addAll(A.get(m).getPremises());
				bodyA.addAll(a.body);
			}

			for (int j = i + 1; j < setOfAttackers.size(); j++) {
				ArrayList<StructuredArgument> B = (ArrayList<StructuredArgument>) setOfAttackers.get(j);
				if (!A.equals(B)) {
					ArrayList<Atom> atomB = new ArrayList<Atom>();
					ArrayList<StructuredArgument> bodyB = new ArrayList<StructuredArgument>();
					for (int m = 0; m < B.size(); m++) {
						StructuredArgument b = B.get(m);
						atomB.addAll(B.get(m).getPremises());
						bodyB.addAll(b.body);
					}

					if ((bodyA.containsAll(bodyB)) && (atomA.containsAll(atomB))) {
						removers.add(setOfAttackers.get(j));
					}
					if ((bodyB.containsAll(bodyA)) && (atomB.containsAll(atomA))) {
						removers.add(setOfAttackers.get(i));
					}
				}
			}
		}
		return removers;

	}

	/*
	 * public static LinkedList<StructuredArgument>
	 * getAttackersFor(StructuredArgument arg, ArrayList SetOfAttacks,
	 * ArrayList<StructuredArgument>ListOfArguments) {
	 * 
	 * Iterator iter = SetOfAttacks.iterator(); LinkedList AttackersFor = new
	 * LinkedList(); LinkedList removes = new LinkedList(); if
	 * (SetOfAttacks.isEmpty() ) { return null; }
	 * 
	 * while (iter.hasNext()){ Attack at = (Attack) iter.next(); if
	 * (at.target.equals(arg)) { AttackersFor.add(at.source); } } /* remove
	 * sub-arguments 1. compute a set of sub-arguments needed to remove 2.
	 */
	/*
	 * removes = getRemoves(AttackersFor); LinkedList temp = AttackersFor; for (int
	 * i=0; i<removes.size(); i++) { temp.remove(removes.get(i)); } AttackersFor =
	 * temp; return AttackersFor; }
	 */

	public static ArrayList<StructuredArgument> removeDuplicates(ArrayList<StructuredArgument> inputList) {
		// Create a HashSet to store unique elements
		HashSet<StructuredArgument> uniqueElements = new HashSet<>();

		// Create a new ArrayList to store the result
		ArrayList<StructuredArgument> resultList = new ArrayList<>();

		// Iterate over the inputList
		for (StructuredArgument element : inputList) {
			// Add the element to the HashSet only if it hasn't been added before
			if (uniqueElements.add(element)) {
				// Add the element to the resultList
				resultList.add(element);
			}
		}

		return resultList;
	}

	public static ArrayList<Attack> GetAttacksFromArg(StructuredArgument a, ArrayList<Attack> S) {
		ArrayList<Attack> result = new ArrayList<Attack>();
		ArrayList<ArrayList<StructuredArgument>> attackersFor = new ArrayList<ArrayList<StructuredArgument>>();
		for (int i = 0; i < S.size(); i++) {
			Attack att = (Attack) S.get(i);
			if (att.target.equals(a)) {
				result.add(att);
				attackersFor.add(att.source);
			}
		}
		return result;
	}

	public static Distance DistFromAtoB(StructuredArgument a, StructuredArgument b, ArrayList<Distance> Dist) {
		Distance result = null;
		for (Distance d : Dist) {
			if ((d.source.equals(a)) & (d.target.equals(b))) {
				result = d;
			}
		}
		return result;
	}

	// public static ArrayList<Attack> ReReach(StructuredArgument a,
	// StructuredArgument b, int n,
	// ArrayList<Attack> S){
	public static void ReReach(StructuredArgument a, StructuredArgument b, int n, ArrayList<Attack> S,
			ArrayList<Attack> Attacks) {
		Visited0 = S;

		// get all attacks having the target as b and the source as c
		ArrayList<Attack> Att = GetAttacksFromArg(b, Attacks);
		// System.out.println("Att: " + Att);
		for (Attack at : Att) {

			for (int i = 0; i < at.source.size(); i++) {
				StructuredArgument c = at.source.get(i);
				if ((Visited0 == null) || (!Visited.contains(at))) {
					if (!Reach.contains(c)) {
						Reach.add(c);
					}
					Distance distance = DistFromAtoB(c, a, Dist);
					distance.dist = n + 1;
					NewDist.add(distance);
					Visited.add(at);
					if (c.equals(a)) {
						continue;
					} else {
						ReReach(a, c, n + 1, Visited, Attacks);
						Visited = Visited0;
					}

				}
			}
		}
	}

	// a0 - a1 - a0
	// - a2 - a0
	// - a4 - a0
	// a4 - a3 - a4
	// - a5 - a0
	// - a3
	// - a6 - a0
	// - a3 - a0
	// - a7 - a0
	// - a4

	public static ArrayList<StructuredArgument> intersection(ArrayList<StructuredArgument> list1,
			ArrayList<StructuredArgument> list2) {
		// Create a HashSet to store unique elements from list1
		HashSet<StructuredArgument> set1 = new HashSet<>(list1);

		// Create a new ArrayList to store the intersection
		ArrayList<StructuredArgument> intersectionList = new ArrayList<>();

		// Iterate over the elements in list2
		for (StructuredArgument element : list2) {
			// Check if the element exists in set1
			if (set1.contains(element)) {
				// Add the element to the intersectionList
				intersectionList.add(element);
				// Remove the element from set1 to avoid duplicates in the intersection
				set1.remove(element);
			}
		}

		return intersectionList;
	}

	public static ArrayList<StructuredArgument> getReachEven(StructuredArgument a, ArrayList<Distance> Dist) {
		ArrayList<StructuredArgument> result = new ArrayList<>();
		for (Distance d : Dist) {
			if ((d.target.equals(a)) & (d.dist % 2 == 0)) {
				if (!result.contains(d.source)) {
					result.add(d.source);
				}
			}
		}
		return result;
	}

	public static ArrayList<StructuredArgument> getReachOdd(StructuredArgument a, ArrayList<Distance> Dist) {
		ArrayList<StructuredArgument> result = new ArrayList<>();
		for (Distance d : Dist) {
			if ((d.target.equals(a)) & (d.dist % 2 != 0)) {
				if (!result.contains(d.source)) {
					result.add(d.source);
				}
			}
		}
		return result;
	}

	public static boolean isIntersectionEmpty(ArrayList<StructuredArgument> list1,
			ArrayList<StructuredArgument> list2) {
		// Create a HashSet to store unique elements from list1
		HashSet<StructuredArgument> set1 = new HashSet<>(list1);

		// Iterate over the elements in list2
		for (StructuredArgument element : list2) {
			// Check if the element exists in set1
			if (set1.contains(element)) {
				// Intersection is not empty
				return false;
			}
		}

		// Intersection is empty
		return true;
	}

	public static ArrayList<ArrayList<StructuredArgument>> computeNotDefBy(ArrayList<StructuredArgument> reachOddOfA,
			ArrayList<ArrayList<StructuredArgument>> extensions, ArrayList<Distance> NewDist) {
		ArrayList<ArrayList<StructuredArgument>> result = new ArrayList<ArrayList<StructuredArgument>>();
		for (ArrayList<StructuredArgument> ext : extensions) {
			ArrayList<StructuredArgument> subResult = new ArrayList<>();
			for (StructuredArgument b : reachOddOfA) {
				ArrayList<StructuredArgument> reachOddOfB = getReachOdd(b, NewDist);
				if (isIntersectionEmpty(ext, reachOddOfB) == true) {
					subResult.add(b);
				}
			}
			if (!(result.contains(subResult))) {
				result.add(subResult);
			}
		}

		return result;
	}

	/*
	 * public static void ExpForScepticalSem(ConjunctiveQuery query, RuleSet
	 * positiveRuleSet, InMemoryAtomSet saturatedAtoms,
	 * ArrayList<ArrayList<StructuredArgument>> extensions,
	 * ArrayList<StructuredArgument> ListArgument, ArrayList<Attack> AttPriority)
	 * throws IteratorException, HomomorphismException { /* ArrayList<Attack>
	 * Visited = new ArrayList<Attack>(); ArrayList<Distance> NewDist = new
	 * ArrayList<Distance>(); ArrayList<StructuredArgument>Reach = new
	 * ArrayList<StructuredArgument>(); ArrayList<Distance> Dist;
	 */

	// ConjunctiveQuery query = DlgpParser.parseQuery("? :- professor(ann).");
	// compute a set of supporting arguments
	// check crecuslous
	// calculate explanation: set of arguments is in each extension

	/*
	 * ArrayList<ArrayList<Argument>> supportingArgs = new
	 * ArrayList<ArrayList<StructuredArgument>>(); supportingArgs =
	 * getArgumentsForQuery(query, positiveRuleSet, saturatedAtoms, supportingArgs);
	 * 
	 * // Check credulous, skepcitcal, non-accept for argument
	 * 
	 * int count = 0; for (StructuredArgument arg : supportingArgs) { for (int i =
	 * 0; i < extensions.size(); i++) { if (extensions.get(i).contains(arg)) {
	 * count++; } } } if ((count == extensions.size()) || (count / extensions.size()
	 * == extensions.size())) { System.out.println("sceptical");
	 * 
	 * Dist = new ArrayList<Distance>(); for (int i = 0; i < ListArgument.size();
	 * i++) { StructuredArgument a = ListArgument.get(i); // Reach.add(a);
	 * Dist.add(new Distance(a, a, 0)); for (int j = 0; j < ListArgument.size();
	 * j++) { if (j != i) { StructuredArgument b = ListArgument.get(j); Dist.add(new
	 * Distance(a, b, 0)); } } }
	 * 
	 * for (int k = 0; k < supportingArgs.size(); k++) { StructuredArgument a =
	 * supportingArgs.get(k); Visited = new ArrayList<Attack>(); NewDist = new
	 * ArrayList<Distance>(); Reach = new ArrayList<StructuredArgument>();
	 * ReReach(a, a, 0, null, Attacks); ArrayList<StructuredArgument> reachEven =
	 * new ArrayList<>(); reachEven = getReachEven(a, NewDist);
	 * ArrayList<StructuredArgument> DefBy = reachEven; // Compute Def for an
	 * argument wrt extensions ArrayList<ArrayList<StructuredArgument>> DefByExt =
	 * new ArrayList<>(); for (int i = 0; i < extensions.size(); i++) {
	 * ArrayList<StructuredArgument> subDef = intersection(DefBy,
	 * extensions.get(i)); DefByExt.add(subDef); } System.out.println("DefBy: " +
	 * DefByExt);
	 * 
	 * // print paths from A to B Graph graph = new Graph(); // addEdge to graph for
	 * (int i = 0; i < AttPriority.size(); i++) { Attack at = (Attack)
	 * AttPriority.get(i); graph.addEdge(at.target, at.source); }
	 * 
	 * StructuredArgument start = a; for (ArrayList<StructuredArgument> notdefby :
	 * DefByExt) { for (StructuredArgument b : notdefby) { StructuredArgument end =
	 * b; System.out.println("All paths from " + start + " to " + end + ":");
	 * graph.printAllPathsOdd(start, end); } } } } }
	 */

	public static HashMap<String, Integer> readPreferenceAtoms(String filePath, AtomSet InitialFacts)
			throws FileNotFoundException, IOException {
		HashMap<String, Integer> preAtoms = new HashMap<>();
		try (BufferedReader reader = new BufferedReader(new FileReader(filePath))) {
			String line;
			while ((line = reader.readLine()) != null) {
				String stBefore = StringUtils.substringBefore(line, " ");
				String stAfter = StringUtils.substringAfter(line, " ");
				CloseableIterator<Atom> it = (CloseableIterator<Atom>) InitialFacts.iterator();
				while (it.hasNext()) {
					String fact = AtomWithoutArity(it.next());
					if (fact.compareTo(stBefore) == 0) {
						preAtoms.put(fact, Integer.valueOf(stAfter));
					}
				}

			}
			reader.close();

		} catch (NumberFormatException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return preAtoms;
	}

	public static boolean includesArrayList(ArrayList<StructuredArgument> mainList,
			ArrayList<StructuredArgument> subList) {
		if (mainList.size() < subList.size()) {
			return false; // If the main list is smaller, it can't include the sub list
		}

		for (int i = 0; i <= mainList.size() - subList.size(); i++) {
			boolean match = true;
			for (int j = 0; j < subList.size(); j++) {
				if (!mainList.get(i + j).equals(subList.get(j))) {
					match = false;
					break;
				}
			}
			if (match) {
				return true;
			}
		}

		return false;
	}

	public static String convertAtom(Atom a) {
		String result;
		if (a.getTerms().size() == 1) {
			result = a.getTerms().toString() + " is " + a.getPredicate().getIdentifier().toString() + " ";
		} else {
			result = a.getTerm(0).toString() + " " + a.getPredicate().getIdentifier().toString() + " "
					+ a.getTerm(1).toString() + " ";
		}
		return result;
	}

	public static String convertNegAtom(Atom a) {
		String result;
		if (a.getTerms().size() == 1) {
			result = a.getTerms().toString() + " cannot be " + a.getPredicate().getIdentifier().toString() + " ";
		} else {
			result = a.getTerm(0).toString() + " does not " + a.getPredicate().getIdentifier().toString() + " "
					+ a.getTerm(1).toString() + " ";
		}
		return result;
	}

	public static String convertListAtoms(ArrayList<Atom> atoms) {
		String result;
		result = convertAtom(atoms.get(0));
		for (int i = 1; i < atoms.size(); i++) {
			result = result + ", we also know that ";
			result = result + convertAtom(atoms.get(i));
		}
		return result;
	}

	public static String convertNegListAtoms(ArrayList<Atom> atoms) {
		String result;
		result = convertNegAtom(atoms.get(0));
		for (int i = 1; i < atoms.size(); i++) {
			result = result + ", we also know that ";
			result = result + convertNegAtom(atoms.get(i));
		}
		return result;
	}

	public static ArrayList<Atom> convertToArrayListAtom(InMemoryAtomSet atoms) throws IteratorException {
		ArrayList<Atom> initialSet = new ArrayList<Atom>();
		CloseableIterator<Atom> it = (CloseableIterator<Atom>) atoms.iterator();
		while (it.hasNext()) {
			initialSet.add(it.next());
		}
		return initialSet;
	}

	private static void printDialogue(List<StructuredArgument> path) {
		if (path.size() % 2 == 0) { // even case
			StructuredArgument a0 = path.get(0);
			if (a0.body.isEmpty()) {
				System.out.println("Explainer: I am certain that " + convertNegAtom(a0.head)); // cannot be an answer
				int size = path.size();
				if (size == 2) {
					System.out.println("Explainee: Why do you think that " + convertNegAtom(path.get(0).head) + "?");
					System.out.println("Explainer: " + convertNegAtom(path.get(0).head) + ", because "
							+ convertAtom(path.get(1).head));
				} else {
					System.out.println("Explainee: Why do you think that " + convertNegAtom(path.get(0).head) + "?");
					int count = 1;
					while (count < path.size()) {
						if (count % 2 != 0) {
							System.out.println("Explainer: " + convertNegAtom(path.get(count - 1).head) + ", because "
									+ convertAtom(path.get(count).head));
						} else {
							System.out.println(
									"Explainee: This is not true, because " + convertAtom(path.get(count).head));
						}
						count++;
					}
					System.out.println("I was right that " + convertNegAtom(path.get(0).head));
				}
				System.out.println("Explainee: Ok! I understood.");
			} else {
				System.out.println("Explainer: I am certain that " + convertNegAtom(a0.head) + ". We also known that "
						+ convertListAtoms(a0.getPremises()));
				int size = path.size();
				if (size == 2) {
					System.out.println("Explainee: Why do you think that " + convertNegAtom(path.get(0).head) + "?");
					System.out.println("Explainer: " + convertNegAtom(path.get(0).head) + ", because "
							+ convertAtom(path.get(1).head));
				} else {
					System.out.println(
							"Explainee: Why do you think that " + convertNegListAtoms(path.get(0).getPremises()));
					int count = 1;
					while (count < path.size()) {
						if (count % 2 != 0) {
							System.out.println("Explainer: " + convertNegListAtoms(path.get(count - 1).getPremises())
									+ ", because " + convertAtom(path.get(count).head));
						} else {
							System.out.println(
									"Explainee: This is not true, because" + convertAtom(path.get(count).head));
						}
						count++;
					}
					System.out.println("I was right that " + path.get(0) + "is not an answer.");
				}
				System.out.println("Explainee: Ok! I understood.");
				System.out.println();
			}
		}

		if (path.size() % 2 != 0) { // odd case
			if (path.get(0).body.isEmpty()) {
				System.out.println("Explainer: I am certain that " + convertAtom(path.get(0).head));
				int count = 1;
				while (count < path.size()) {
					if (count % 2 == 0) {
						System.out.println("Explainer: " + convertNegAtom(path.get(count - 1).head) + ", because "
								+ convertAtom(path.get(count).head));
					} else {
						System.out.println("Explainee: That is not true. " + convertNegAtom(path.get(count - 1).head)
								+ ", because " + convertAtom(path.get(count).head));
					}
					if (count == path.size() - 1) {
						System.out.println("I was right that " + convertAtom(path.get(0).head));
					}
					count++;
				}
			} else {
				System.out.println("Explainer: I am certain that " + convertAtom(path.get(0).head)
						+ ", because we also know that " + convertListAtoms(path.get(0).getPremises()));
				int count = 1;
				while (count < path.size()) {
					if (count % 2 == 0) {
						System.out.println("Explainer: " + convertNegListAtoms(path.get(count - 1).getPremises())
								+ ", because " + convertAtom(path.get(count).head));
					} else {
						System.out.println(
								"Explainee: That is not true. " + convertNegListAtoms(path.get(count - 1).getPremises())
										+ ", because " + convertAtom(path.get(count).head));
					}
					if (count == path.size() - 1) {
						System.out.println("I was right that " + convertAtom(path.get(0).head));
					}
					count++;
				}
			}

			System.out.println("Explainee: Ok! I understand.");
			System.out.println();
		}

	}

}
