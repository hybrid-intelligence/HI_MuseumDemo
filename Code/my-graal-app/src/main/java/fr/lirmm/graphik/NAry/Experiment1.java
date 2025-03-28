package fr.lirmm.graphik.NAry;

import java.io.BufferedWriter;
import java.io.FileWriter;
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
import java.util.Queue;
import java.util.Set;
import java.util.Stack;
import java.util.function.Function;
import java.util.stream.*;


import org.apache.commons.compress.harmony.pack200.NewAttribute;
import org.tweetyproject.graphs.HyperDirEdge;
import org.tweetyproject.graphs.HyperGraph;
import org.tweetyproject.graphs.util.GraphUtil;


import ch.qos.logback.core.pattern.parser.Node;
import fr.lirmm.graphik.DEFT.core.DefeasibleKB;
import fr.lirmm.graphik.NAry.ArgumentationFramework.StructuredArgument;
import fr.lirmm.graphik.NAry.ArgumentationFramework.ArgumentNode;
import fr.lirmm.graphik.NAry.ArgumentationFramework.ArgumentTree;
import fr.lirmm.graphik.NAry.ArgumentationFramework.Attack;
import fr.lirmm.graphik.graal.api.backward_chaining.QueryRewriter;
import fr.lirmm.graphik.graal.api.core.Atom;
import fr.lirmm.graphik.graal.api.core.AtomSet;
import fr.lirmm.graphik.graal.api.core.AtomSetException;
import fr.lirmm.graphik.graal.api.core.ConjunctiveQuery;
import fr.lirmm.graphik.graal.api.core.InMemoryAtomSet;
import fr.lirmm.graphik.graal.api.core.Predicate;
import fr.lirmm.graphik.graal.api.core.Rule;
import fr.lirmm.graphik.graal.api.core.RuleSet;
import fr.lirmm.graphik.graal.api.core.Substitution;
import fr.lirmm.graphik.graal.api.forward_chaining.ChaseException;
import fr.lirmm.graphik.graal.api.homomorphism.HomomorphismException;
import fr.lirmm.graphik.graal.backward_chaining.pure.PureRewriter;
import fr.lirmm.graphik.graal.core.atomset.LinkedListAtomSet;
import fr.lirmm.graphik.graal.core.ruleset.LinkedListRuleSet;
import fr.lirmm.graphik.graal.homomorphism.SmartHomomorphism;
import fr.lirmm.graphik.graal.io.dlp.DlgpParser;
import fr.lirmm.graphik.util.stream.CloseableIterator;
import fr.lirmm.graphik.util.stream.IteratorException;


public class Experiment1 {
	//static private String file = "C:/Users/tho310/Data test/test1.dlgp";
	static private String file = "C:/Users/tho310/Data test/Museum Case/CKG-Inconsistency.dlgp";

	public static ArrayList<StructuredArgument> listArguments;
	public static Set<StructuredArgument> arguments;
	//// Initialise an attack set
	public static Set<Attack> attackSet;

	// private static int count;

	public static <T> void main(String[] args)
			throws AtomSetException, ChaseException, HomomorphismException, IOException {
		// TODO Auto-generated method stub
		DefeasibleKB kb = new DefeasibleKB(file);
		DefeasibleKB kbArgs = new DefeasibleKB(file);
		AtomSet initialFacts = new LinkedListAtomSet();
		RuleSet negativeRuleSet = new LinkedListRuleSet();
		RuleSet positiveRuleSet = new LinkedListRuleSet();
		InMemoryAtomSet saturatedAtoms = new LinkedListAtomSet();
		attackSet = new HashSet<Attack>();

		kbArgs.saturate();
		saturatedAtoms.addAll(kbArgs.facts);
		System.out.println("Saturated Facts: " + saturatedAtoms);
		// kbArgs.unsaturate();
		// System.out.println("Chase" + saturatedAtoms);

		initialFacts.addAll(kb.facts);
		negativeRuleSet = kb.negativeConstraintSet;
		positiveRuleSet = kb.rules;

		for (Rule r : negativeRuleSet) {
			System.out.println(r);
			System.out.println(r.getBody().getVariables());
		}

		long startTime = System.currentTimeMillis(); // Get the start time
		listArguments = computeArguments.generateArgs(kbArgs);

		// Check whether premises of arguments are consistent
		// If Yes, remove it from ListArgument, otherwise, keep it.

		AtomSet Test;
		for (int i = listArguments.size() - 1; i >= 0; i--) {
			Test = new LinkedListAtomSet();
			for (Atom p : ((StructuredArgument) listArguments.get(i)).getPremises()) {
				Test.add(p);
			}
			kbArgs.strictAtomSet = Test;
			if (App1.RIncosistent(kbArgs)) {
				listArguments.remove(i);
			}
		}

		long endTime = System.currentTimeMillis(); // Get the end time
		long duration = endTime - startTime; // Calculate the duration

		/*
		 * for (StructuredArgument a : listArguments) { System.out.println(a); }
		 */

		Set<ArgumentTree> trees = new HashSet<ArgumentTree>();
		ArrayList<Integer> heights = new ArrayList<Integer>();
		ArrayList<Integer> widths = new ArrayList<Integer>();

		long startTime1 = System.currentTimeMillis();

		// compute all minimal conflicts
		Set<AtomSet> minInconSets = FindMinIncSets.findMinimalIncSubsets(kb);
		System.out.println("minimal inconsistent subsets: \n " + minInconSets + " \n size: " + minInconSets.size());

		int number = 0;

		for (StructuredArgument argRoot : listArguments) {
			number++;
			if (number % 100 == 0) {
				System.out.println("Running so far " + number);
			}

			ArgumentTree tree = getArgumentTree(argRoot, minInconSets, listArguments, arguments, attackSet, kb);
			trees.add(tree);
		}

		long endTime1 = System.currentTimeMillis();
		long duration1 = endTime1 - startTime1;

		/*
		 * System.out.println("Argument: " + listArguments);
		 * System.out.println("Attack: " + attackSet);
		 * 
		 * SetAf s = new SetAf(); s = convertToSetAf(listArguments, attackSet);
		 * SimpleGroundedSetAfReasoner gr = new SimpleGroundedSetAfReasoner();
		 * SimpleAdmissibleSetAfReasoner ad = new SimpleAdmissibleSetAfReasoner();
		 * SimplePreferredSetAfReasoner pr = new SimplePreferredSetAfReasoner();
		 * System.out.println("grounded: " + gr.getModel(s));
		 * System.out.println("admissible: " + ad.getModels(s));
		 * System.out.println("preferred: " + pr.getModels(s));
		 */

		try (BufferedWriter writer = new BufferedWriter(new FileWriter("execution_time.txt"))) {
			writer.write("minimal inconsistent subsets: \n " + minInconSets.size());
			for (ArgumentTree t : trees) {
				writer.write("\n Argument tree for " + t.getRoot() + "\n");
				//writer.write("Nodes: " + t.getNumberOfNodes() + " Edges: " + t.getNumberOfEdges() + "\n");
				//writer.write("Height: " + t.getHeight());
				heights.add(t.getHeight());
				//writer.write(" Width: " + t.getMaxWidth() + "\n");
				widths.add(t.getMaxWidth());
				t.printTree(t.getRoot(), writer);
			}

			writer.write("\nNumber of trees " + trees.size() + "\n");
			writer.write("Execution time for computing trees " + duration1 + "\n");
			// System.out.println("Number of trees " + trees.size());

			int[] result = findMaxAndMin(heights);
			writer.write("Max of heights: " + result[0] + "\n");
			writer.write("Min of heights: " + result[1] + "\n");

			double averageHeight = calculateAverage(heights);
			writer.write("Average Tree Height: " + averageHeight + "\n");

			// Print out the frequencies
			Map<Integer, Integer> frequencyHeight = countFrequencies(heights);
			for (Map.Entry<Integer, Integer> entry : frequencyHeight.entrySet()) {
				writer.write("Element: " + entry.getKey() + ", Frequency- Height: " + entry.getValue() + ". ");
			}

			int[] result1 = findMaxAndMinWidth(widths);
			writer.write("Max of Widths: " + result1[0] + "\n");
			writer.write("Min of Widths: " + result1[1] + "\n");

			double averageWidth = calculateAverage(widths);
			writer.write("Average Tree Width: " + averageWidth + "\n");

			// Print out the frequencies
			Map<Integer, Integer> frequencyWidths = countFrequencies(widths);
			for (Map.Entry<Integer, Integer> entryW : frequencyWidths.entrySet()) {
				writer.write("Element: " + entryW.getKey() + ", Frequency - width: " + entryW.getValue() + ". ");
			}

			writer.write("Number of args: " + listArguments.size() + " - Execution time for translating arguments: "
					+ duration + "\n");
			for (StructuredArgument a : listArguments) { 
				writer.write(a.toString() + "\n"); 
				}
			writer.write("Number of attacks: " + attackSet.size());
			System.out.println("Attacks:" + attackSet);
			writer.flush(); // Close the BufferedWriter
			writer.close();
		}

		/*
		 * String queryString = "? :- postdoc(ann)."; ConjunctiveQuery query =
		 * DlgpParser.parseQuery(queryString); AtomSet qAtom = query.getAtomSet();
		 * ArrayList<ArrayList<StructuredArgument>> proArgs =
		 * App1.getArgsForAtomSet(qAtom, listArguments);
		 * 
		 * System.out.println("Proponent arguments: " + proArgs); Argument argRoot =
		 * proArgs.get(0).get(0); System.out.println(argRoot);
		 * 
		 */

		/*
		 * for (StructuredArgument argRoot : listArguments) { // StructuredArgument
		 * argRoot = listArguments.get(5); // initialise an argument tree for a given
		 * argument (root). ArgumentNode root = new ArgumentNode(argRoot); ArgumentTree
		 * argTree = new ArgumentTree(root); argTree.add(root);
		 * System.out.println("Root: " + argTree.getRoot() + " Id " +
		 * argTree.getRoot().getNodeID());
		 * 
		 * Set<AtomSet> firstLevelSets = new HashSet<AtomSet>(); firstLevelSets =
		 * firstLevel(argRoot, minInconSets); //
		 * System.out.println("first level conflict sets: " + firstLevelSets + "\n");
		 * 
		 * for (AtomSet set : firstLevelSets) { count = 0; // Construct Atoms of
		 * Undercut (Counter-Argument) for root. Set<Atom> undercutAtoms = new
		 * HashSet<Atom>();
		 * 
		 * // Convert AtomSet to Set<Atom>
		 * 
		 * CloseableIterator<Atom> it = set.iterator(); while (it.hasNext()) {
		 * undercutAtoms.add(it.next()); }
		 * 
		 * // remove all atoms in the root from the current minimal conflicts.
		 * 
		 * for (Atom premise : argRoot.getPremises()) { undercutAtoms.remove(premise); }
		 * 
		 * // Get arguments that have the atom of "undercut" in their premises
		 * ArrayList<ArrayList<StructuredArgument>> setOfUndercuts = new
		 * ArrayList<ArrayList<StructuredArgument>>();
		 * 
		 * setOfUndercuts.addAll(findArgumentSets(undercutAtoms, listArguments));
		 * 
		 * // System.out.println("Set of undercuts: " + setOfUndercuts);
		 * 
		 * // Create and Add the Undercut Node:
		 * 
		 * for (ArrayList<StructuredArgument> undercut : setOfUndercuts) {
		 * 
		 * count = 1;
		 * 
		 * // Initialise a defence set and a culprit Set<StructuredArgument> defenceSet
		 * = new HashSet<StructuredArgument>(); Set<StructuredArgument> culprit = new
		 * HashSet<StructuredArgument>(); defenceSet.add(argRoot);
		 * culprit.addAll(undercut); // add undercut to culprit //
		 * System.out.println("Culprit: " + culprit + " " + count);
		 * 
		 * // Process undercuts and ensure undercutNodes are only added once
		 * Set<ArgumentNode> undercutNodes = new HashSet<ArgumentNode>(); for
		 * (StructuredArgument argument : undercut) { ArgumentNode newNode = new
		 * ArgumentNode(argument); argTree.add(newNode); // Add the new node to the tree
		 * undercutNodes.add(newNode); // Add node to the set to create hyperedegs }
		 * 
		 * // Create hyperedges String label = ".."; argTree.add(new
		 * HyperDirEdge<ArgumentNode>(undercutNodes, root, label));
		 * 
		 * // add to the attack set. Attack attack = new Attack(undercut, argRoot);
		 * attackSet.add(attack);
		 * 
		 * // Work with remaining sets, but avoid modifying the original list
		 * ArrayList<AtomSet> remainingMins = new ArrayList<>(minInconSets);
		 * remainingMins.remove(set);
		 * 
		 * // System.out.println("remainingMins: " + remainingMins + " size " + //
		 * remainingMins.size());
		 * 
		 * for (ArgumentNode node : undercutNodes) { subcuts(node, remainingMins, set,
		 * new HashSet<>(root.getPremises()), argTree, defenceSet, culprit); //
		 * subcuts(node, remainingMins, set, new HashSet<>(node.getPremises()), //
		 * argTree); } } } }
		 * 
		 * System.out.println(" \n Argument tree for " + argTree.getRoot() + " ID " +
		 * argTree.getRoot().getNodeID()); argTree.printTree(argTree.getRoot());
		 * System.out.print("Nodes: " + argTree.getNumberOfNodes() + " .Edges: " +
		 * argTree.getNumberOfEdges() + "\n"); System.out.println("Width: " +
		 * argTree.getMaxWidth()); System.out.println("Height: " + argTree.getHeight());
		 * }
		 */
	}

	// function finds an average height of argumentation trees

	public static double calculateAverage(ArrayList<Integer> heights) {
		if (heights == null || heights.isEmpty()) {
			throw new IllegalArgumentException("List cannot be null or empty");
		}

		int sum = 0;
		for (int height : heights) {
			sum += height;
		}

		return (double) sum / heights.size();
	}

	/**
	 * 
	 * @param list of heights of argumentation trees
	 * @return maximal and minimal heights.
	 */

	public static int[] findMaxAndMin(ArrayList<Integer> list) {
		if (list == null || list.isEmpty()) {
			throw new IllegalArgumentException("List cannot be null or empty");
		}

		int max = Collections.max(list);
		int min = Collections.min(list);

		return new int[] { max, min };
	}

	// function find an average width of argumentation trees

	public static double calculateAverageWidth(ArrayList<Integer> widths) {
		if (widths == null || widths.isEmpty()) {
			throw new IllegalArgumentException("List cannot be null or empty");
		}

		int sum = 0;
		for (int width : widths) {
			sum += width;
		}

		return (double) sum / widths.size();
	}

	// find maximal and minimal widths

	public static int[] findMaxAndMinWidth(ArrayList<Integer> list) {
		if (list == null || list.isEmpty()) {
			throw new IllegalArgumentException("List cannot be null or empty");
		}

		int max = Collections.max(list);
		int min = Collections.min(list);

		return new int[] { max, min };
	}

	/**
	 * 
	 * @param an   argument
	 * @param myID
	 * @return the argument tree for a given argument
	 * @throws IteratorException
	 * @throws AtomSetException 
	 */

	public static ArgumentTree getArgumentTree(StructuredArgument argRoot, Set<AtomSet> minInconSets,
			ArrayList<StructuredArgument> listArguments, Set<StructuredArgument> arguments, Set<Attack> attackSet, DefeasibleKB kb) throws IteratorException, AtomSetException {

		// Initialise an argument tree for a given argument (root).
		ArgumentNode root = new ArgumentNode(argRoot);
		ArgumentTree argTree = new ArgumentTree(root);
		argTree.add(root);
		

		// 1) Collect all MISs that include argRoot
		Set<AtomSet> firstLevelSets = new HashSet<AtomSet>();
		firstLevelSets = firstLevel(argRoot, minInconSets);

		// 2) Create argument tree recursively

		for (AtomSet set : firstLevelSets) {

			// Collect all possible undercuts (Counter-Argument) for root.
			Set<Atom> undercutAtoms = new HashSet<>();

			// Convert AtomSet to Set<Atom>
			CloseableIterator<Atom> it = set.iterator();
			while (it.hasNext()) {
				Atom atom = it.next();
				undercutAtoms.add(atom);
			}

			// Remove all atoms in the root's premises from the current MICs.
			undercutAtoms.removeAll(argRoot.getPremises());

			// Get arguments that have the atom of "undercut" in their premises
			ArrayList<ArrayList<StructuredArgument>> setOfUndercuts = new ArrayList<ArrayList<StructuredArgument>>();
			setOfUndercuts.addAll(findArgumentSets(undercutAtoms, listArguments));

			// Initialise a defence set and a culprit
			Set<StructuredArgument> defenceSet = new HashSet<StructuredArgument>();
			Set<StructuredArgument> culprit = new HashSet<StructuredArgument>();
			defenceSet.add(argRoot);
			arguments.add(argRoot);

			if (!setOfUndercuts.isEmpty()) {

				// Create and Add the Undercut Node:
				for (ArrayList<StructuredArgument> undercut : setOfUndercuts) {
					// count = 1;

					// Set<StructuredArgument> defenceSet = new HashSet<StructuredArgument>();
					// Set<StructuredArgument> culprit = new HashSet<StructuredArgument>();
					// defenceSet.add(argRoot);
					culprit.addAll(undercut);
					arguments.addAll(undercut);

					// Process undercuts and ensure undercutNodes are only added once
					Set<ArgumentNode> undercutNodes = new HashSet<ArgumentNode>();
					for (StructuredArgument argument : undercut) {
						ArgumentNode newNode = new ArgumentNode(argument);
						argTree.add(newNode); // Add the new node to the tree
						undercutNodes.add(newNode); // Add node to the set to create hyperedegs

					}

					// Create hyperedges
					String label = attackEdges(set, kb.negativeConstraintSet);
					argTree.add(new HyperDirEdge<ArgumentNode>(undercutNodes, root, label));

					// add to the attack set.
					Attack attack = new Attack(undercut, argRoot);
					attackSet.add(attack);

					// Work with remaining sets, but avoid modifying the original list
					ArrayList<AtomSet> remainingMins = new ArrayList<>(minInconSets);
					remainingMins.remove(set);

					for (ArgumentNode node : undercutNodes) {
						subcuts(node, remainingMins, set, new HashSet<>(node.getPremises()), argTree, defenceSet,
								culprit, listArguments, arguments, attackSet, 2, minInconSets, kb);
					}
				}
			}

		}
		return argTree;
	}

	private static ArgumentNode findNodeByID(ArgumentTree argTree, int myID) {
		for (ArgumentNode node : argTree.getNodes()) {
			if (node.getArgID() == myID) {
				return node; // Return the node if found
			}
		}
		return null; // Return null if not found
	}

	/**
	 * This method returns the minimal conflicts that can be used to construct
	 * undercuts to the given argument.
	 * 
	 * @param arg some argument.
	 * @return a set of minimal conflicts.
	 * @throws IteratorException
	 */
	public static Set<AtomSet> firstLevel(StructuredArgument arg, Set<AtomSet> allMins) throws IteratorException {
		Stack<AtomSet> candidates = new Stack<AtomSet>();
		for (AtomSet min : allMins) {
			ArrayList<Atom> set = new ArrayList<Atom>();

			CloseableIterator<Atom> it = min.iterator();
			while (it.hasNext()) {
				set.add(it.next());
			}

			set.retainAll(arg.getPremises());
			if (!set.isEmpty())
				candidates.add(min);
		}
		Set<AtomSet> result = new HashSet<AtomSet>();
		while (!candidates.isEmpty()) {
			AtomSet element = candidates.pop();
			boolean addToResult = true;
			for (AtomSet element2 : candidates) {
				Set<Atom> set1 = new HashSet<Atom>();
				Set<Atom> set2 = new HashSet<Atom>();

				// Convert AtomSet to Set<Atom>

				CloseableIterator<Atom> it = element.iterator();
				while (it.hasNext()) {
					set1.add(it.next());
				}

				CloseableIterator<Atom> it2 = element2.iterator();
				while (it2.hasNext()) {
					set1.add(it2.next());
				}

				set1.removeAll(arg.getPremises());
				set2.removeAll(arg.getPremises());
				if (set2.containsAll(set1)) {
					addToResult = false;
					break;
				}
			}
			if (addToResult)
				for (AtomSet element2 : result) {
					Set<Atom> set1 = new HashSet<Atom>();
					Set<Atom> set2 = new HashSet<Atom>();

					// Convert AtomSet to Set<Atom>

					CloseableIterator<Atom> it = element.iterator();
					while (it.hasNext()) {
						set1.add(it.next());
					}

					CloseableIterator<Atom> it2 = element2.iterator();
					while (it2.hasNext()) {
						set1.add(it2.next());
					}

					set1.removeAll(arg.getPremises());
					set2.removeAll(arg.getPremises());
					if (set2.containsAll(set1)) {
						addToResult = false;
						break;
					}
				}
			if (addToResult)
				result.add(element);
		}
		return result;
	}

	/**
	 * This method return sets of arguments whose the head equal to a set of atoms
	 * 
	 */

	public static ArrayList<ArrayList<StructuredArgument>> findArgumentSets(Set<Atom> atoms,
			ArrayList<StructuredArgument> listOfArgs) {
		// Step 1: Group Arguments by Atom conclusion
		Map<Atom, List<StructuredArgument>> atomToArgumentsMap = new HashMap<>();
		for (StructuredArgument argument : listOfArgs) {
			Atom conclusion = argument.head;
			atomToArgumentsMap.computeIfAbsent(conclusion, k -> new ArrayList<>()).add(argument);
		}

		// Step 2: Collect relevant argument groups based on the input set of atoms
		List<List<StructuredArgument>> argumentGroups = new ArrayList<>();
		for (Atom atom : atoms) {
			if (atomToArgumentsMap.containsKey(atom)) {
				argumentGroups.add(atomToArgumentsMap.get(atom));
			}
		}

		// Step 3: Generate all combinations across argument groups
		ArrayList<ArrayList<StructuredArgument>> result = new ArrayList<>();
		generateCombinations(argumentGroups, result, new ArrayList<>(), 0);

		return result;
	}

	private static void generateCombinations(List<List<StructuredArgument>> groups,
			ArrayList<ArrayList<StructuredArgument>> result, ArrayList<StructuredArgument> current, int depth) {
		if (depth == groups.size()) {
			result.add(new ArrayList<>(current)); // Add completed combination to result
			return;
		}

		for (StructuredArgument arg : groups.get(depth)) {
			current.add(arg);
			generateCombinations(groups, result, current, depth + 1);
			current.remove(current.size() - 1); // Backtrack
		}
	}

	/**
	 * This method recursively builds up the argument tree from the given argument.
	 * 
	 * @param argNode        an argument.
	 * @param remainingNodes the non-visited minimal conflict sets.
	 * @param current        the current node.
	 * @param currentSupport the union of the supports of the current path.
	 * @param argTree        the argument tree.
	 * @throws IteratorException
	 * @throws AtomSetException 
	 */
	private static void subcuts(ArgumentNode currentNode, ArrayList<AtomSet> remainingMins, AtomSet current,
			Set<Atom> supportOfCurrentNode, ArgumentTree argTree, Set<StructuredArgument> defenceSet,
			Set<StructuredArgument> culprit, ArrayList<StructuredArgument> listArguments, Set<StructuredArgument> arguments, Set<Attack> attackSet, int level,
			Set<AtomSet> minInconSets, DefeasibleKB kb) throws IteratorException, AtomSetException {

		boolean allIntersectionsEmpty = true;
		for (AtomSet nextMin : remainingMins) {

			// Convert Atomset to a Set to optimize intersection check
			Set<Atom> convertMin = new HashSet<Atom>();
			CloseableIterator<Atom> it = nextMin.iterator();
			while (it.hasNext()) {
				convertMin.add(it.next());
			}

			// check current and node have a non-empty intersection
			if (hasNonEmptyIntersection(current, convertMin)) {

				// Check whether the support of the current node is present in the MinSets.
				if (!supportOfCurrentNode.containsAll(convertMin)) {
					Set<Atom> set = new HashSet<Atom>(currentNode.getPremises());
					set.retainAll(convertMin);

					if (!set.isEmpty()) {
						boolean properUndercut = true;

						/**
						 * The idea is to ensure that the current set (current) is not contradicted by
						 * other supporting evidence elsewhere, which would invalidate the undercut.
						 */						
						
						for (AtomSet min2 : remainingMins) {
						    if (!min2.equals(nextMin) && current.equals(min2)) {
						        // Convert AtomSet to a Set<Atom> for efficient operations
						        Set<Atom> minSet2 = toSet(min2);

						        // Compute intersections with currentNode.getPremises()
						        Set<Atom> intersection1 = new HashSet<>(convertMin);
						        intersection1.retainAll(currentNode.getPremises());

						        Set<Atom> intersection2 = new HashSet<>(minSet2);
						        intersection2.retainAll(currentNode.getPremises());

						        // Check if intersection1 contains all elements of intersection2
						        if (intersection1.containsAll(intersection2)) {
						            properUndercut = false;
						            break;
						        }
						    }
						}

						if (properUndercut) {
							Set<Atom> atomsUndercut = new HashSet<Atom>(convertMin);
							atomsUndercut.removeAll(currentNode.getPremises());

							// Get a set of arguments that collectively attacks argNode
							ArrayList<ArrayList<StructuredArgument>> undercuts = findArgumentSets(atomsUndercut, listArguments);

							// Create argumentNodes and hyperdeges of the argTree.
							for (ArrayList<StructuredArgument> undercut : undercuts) {
								arguments.addAll(undercut);
								Set<ArgumentNode> undercutNodes = new HashSet<ArgumentNode>();
								
								// Get body in the support of arg in the defence set, culprit, and undercut
						        Set<StructuredArgument> supDefSet = getSupport(defenceSet);
						        Set<StructuredArgument> supCulprit = getSupport(culprit);
						        ArrayList<StructuredArgument> supUndercut = getSupport(undercut);						

								// Opponent's moves: (1) opponent's move can not repeat proponent's move
								// (2) opponent's move can not repeat the previous opponent's move
						        if (level % 2 != 0 && (compareSets(defenceSet, undercut) 
						        						|| compareSets(supDefSet, undercut)
						        						|| compareSets(defenceSet, supUndercut) 
						        						|| compareSets(culprit, undercut)
						        						|| compareSets(supCulprit, undercut) 
						        						|| checkInc(culprit, undercut, minInconSets))) {
						            break;
						        }

								// Proponent's moves: (1) proponent's move can not repeat opponent's move
								// (2) proponent's move can not conflict to any argument in the defence set
						        if (level % 2 == 0 && (compareSets(culprit, undercut) 
						        					|| compareSets(supCulprit, undercut)
						        					|| checkInc(defenceSet, undercut, minInconSets))) {
						            break;
						        }
								allIntersectionsEmpty = false;

								// Add nodes
								for (StructuredArgument arg : undercut) {
									ArgumentNode newNode = new ArgumentNode(arg);
									undercutNodes.add(newNode);
									argTree.add(newNode);
								}
								
								// Add hyperedges
								String label2 = attackEdges(nextMin, kb.negativeConstraintSet);
								argTree.add(new HyperDirEdge<ArgumentNode>(undercutNodes, currentNode, label2));

								// Add to the culprit or the defence set
								for (ArgumentNode node : undercutNodes) {
						            StructuredArgument arg = returnArgForNode(node, listArguments);
						            if (level % 2 == 0) {
						                defenceSet.add(arg);
						            } else {
						                culprit.add(arg);
						            }
						        }

								// Add to the attack set
						        StructuredArgument currentArg = returnArgForNode(currentNode, listArguments);
						        attackSet.add(new Attack(undercut, currentArg));
						        
						        // Recursively process subcuts
								ArrayList<AtomSet> newRemainingMins = new ArrayList<AtomSet>(remainingMins);
								newRemainingMins.remove(nextMin);

								for (ArgumentNode node : undercutNodes) {
									Set<Atom> newSupport = new HashSet<Atom>(atomsUndercut); // Create the new support
									newSupport.addAll(node.getPremises());
									subcuts(node, newRemainingMins, nextMin, newSupport, argTree, defenceSet, culprit,
											listArguments, arguments, attackSet, level + 1, minInconSets, kb);
								}
							}
						} // End For

					} // End IF

				} // End IF

			} // End If
		} // End For
		
//		if (allIntersectionsEmpty) {
//		    // Proponent repeating their argument to defend itself (A attacks B and B attacks A)
//		    if (level == 2) {
//		        StructuredArgument currentArg = returnArgForNode(currentNode, listArguments);
//		        Set<Atom> setAtoms = new HashSet<>();
//
//		        // Add the head of the current argument and the root argument's head to the set
//		        if (currentArg.getPremises().isEmpty()) {
//		            setAtoms.add(currentArg.head);
//		        } else {
//		            setAtoms.addAll(currentArg.getPremises());
//		        }
//		        setAtoms.add(argTree.getRoot().getHead());
//
//		        // Check if ALL elements in any of the minInconSets are contained in setAtoms
//		                boolean allElementsContained = minInconSets.stream()
//		                        .anyMatch(element -> {
//		                            Set<Atom> elementAtoms = new HashSet<>();
//		                            try (CloseableIterator<Atom> iterator = element.iterator()) {
//		                                try {
//											while (iterator.hasNext()) {
//											    elementAtoms.add(iterator.next());
//											}
//										} catch (IteratorException e) {
//											e.printStackTrace();
//										}
//		                            }
//		                            return elementAtoms.containsAll(setAtoms);
//		                        });
//
//		        // If ALL elements in current are contained in setAtoms, add hyperedge
//		        if (allElementsContained) {
//		            StructuredArgument previousArg = returnArgForNode(argTree.getRoot(), listArguments);
//		            ArgumentNode newNode = new ArgumentNode(previousArg);
//		            argTree.add(newNode);
//		            argTree.add(new HyperDirEdge<>(newNode, currentNode));
//		        }
//		    }
//		}

	}
	
	private static String attackEdges(AtomSet set, RuleSet negativeRuleSet) throws AtomSetException {
	    String result = null;
	    Set<Predicate> predicates = set.getPredicates();
	    
	    Iterator<Rule> it1 = negativeRuleSet.iterator();
	    while (it1.hasNext()) {
	        Rule r = it1.next();
	        if (r.getBody().getPredicates().equals(predicates)) {
	            result = r.toString();
	        }
	    }
	    
	    return result;
	}
	
	//Helper method to convert AtomSet to Set<Atom>
	private static Set<Atom> toSet(AtomSet atomSet) throws IteratorException {
	    Set<Atom> set = new HashSet<>();
	    try (CloseableIterator<Atom> iterator = atomSet.iterator()) {
	        while (iterator.hasNext()) {
	            set.add(iterator.next());
	        }
	    }
	    return set;
	}
	
	private static Set<StructuredArgument> getSupport(Collection<StructuredArgument> arguments) {
	    Set<StructuredArgument> support = new HashSet<>();
	    for (StructuredArgument arg : arguments) {
	        support.addAll(findAllArgsBody(arg));
	    }
	    return support;
	}

	private static ArrayList<StructuredArgument> getSupport(ArrayList<StructuredArgument> arguments) {
		ArrayList<StructuredArgument> support = new ArrayList<>();
	    for (StructuredArgument arg : arguments) {
	        support.addAll(findAllArgsBody(arg));
	    }
	    return support;
	}

	public static boolean hasNonEmptyIntersection(AtomSet set1, Set<Atom> set2) throws IteratorException {
		// Convert one of the LinkedLists to a Set to optimize intersection check
		Set<Atom> set1AsSet = new HashSet<>();
		CloseableIterator<Atom> it1 = set1.iterator();
		while (it1.hasNext()) {
			set1AsSet.add(it1.next());
		}

		Set<Atom> temp = new HashSet<>(set1AsSet);

		// Retain elements that are common in both sets
		temp.retainAll(set2);

		// Check if the intersection is non-empty
		return !temp.isEmpty();
	}

	private static StructuredArgument returnArgForNode(ArgumentNode node, ArrayList<StructuredArgument> listOfArgs) {
		StructuredArgument result = new StructuredArgument();
		for (StructuredArgument arg : listOfArgs) {
			if (arg.myID == node.getArgID()) {
				result = arg;
				break;
			}
		}
		return result;
	}
	
	private static boolean compareSets(Set<StructuredArgument> A, List<StructuredArgument> B) {
	    return B.stream().anyMatch(A::contains);
	}

	private static boolean compareAtoms(Set<StructuredArgument> A, ArrayList<StructuredArgument> B) {

		for (StructuredArgument argB : B) {
			if (A.contains(argB)) {
				return true;
			}
		}
		return false;

	}

	private static boolean checkInc(Set<StructuredArgument> A, ArrayList<StructuredArgument> setB,
			Set<AtomSet> minInconSets) throws IteratorException {
		// Combine premises from setB and A into a single Set<Atom> for faster lookups
			Set<Atom> combined = new HashSet<>();
			addAtomsToSet(setB, combined);
		    addAtomsToSet(A, combined);

		// Check if any AtomSet in minInconSets is fully contained in combinedPremises
		    for (AtomSet atomSet : minInconSets) {
		        if (isAtomSetContained(atomSet, combined)) {
		            return true;
		        }
		    }
		return false; // No matching AtomSet found
	}
	
	private static void addAtomsToSet(Collection<StructuredArgument> arguments, Set<Atom> atomSet) {
	    for (StructuredArgument arg : arguments) {
	        if (!arg.body.isEmpty()) {
	            atomSet.addAll(arg.getPremises());
	        } else {
	            atomSet.add(arg.head);
	        }
	    }
	}
	
	private static boolean isAtomSetContained(AtomSet atomSet, Set<Atom> atomSetToCheck) throws IteratorException {
	    try (CloseableIterator<Atom> iterator = atomSet.iterator()) {
	        while (iterator.hasNext()) {
	            if (!atomSetToCheck.contains(iterator.next())) {
	                return false; // Early exit if any atom is not found
	            }
	        }
	    }
	    return true; // All atoms in the AtomSet are found
	}


	public static List<StructuredArgument> findAllArgsBody(StructuredArgument argument) {
		List<StructuredArgument> arguments = new ArrayList<>();
		findArgumentsRecursively(argument, arguments);
		return arguments;
	}

	private static void findArgumentsRecursively(StructuredArgument argument, List<StructuredArgument> argBody) {
		if (argument.body.isEmpty()) {
			return; // Base case: Stop if the argument is null (empty body)
		}
		argBody.addAll(argument.body); // Add the current argument to the list
		for (StructuredArgument arg : argument.body) {
			findArgumentsRecursively(arg, argBody); // Recursively process the body
		}
	}

	private static Map<Integer, Integer> countFrequencies(ArrayList<Integer> list) {
		Map<Integer, Integer> frequencyMap = new HashMap<>();

		// Loop through the list and count the occurrences of each element
		for (Integer num : list) {
			frequencyMap.put(num, frequencyMap.getOrDefault(num, 0) + 1);
		}

		return frequencyMap;
	}

}
