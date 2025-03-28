package fr.lirmm.graphik.NAry;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;

import fr.lirmm.graphik.DEFT.core.DefeasibleKB;
import fr.lirmm.graphik.DEFT.gad.Derivation;
import fr.lirmm.graphik.DEFT.gad.GADEdge;
import fr.lirmm.graphik.NAry.ArgumentationFramework.StructuredArgument;
import fr.lirmm.graphik.graal.api.core.Atom;
import fr.lirmm.graphik.graal.api.core.AtomSetException;
import fr.lirmm.graphik.graal.api.core.Predicate;
import fr.lirmm.graphik.graal.api.forward_chaining.ChaseException;
import fr.lirmm.graphik.graal.api.homomorphism.HomomorphismException;
import fr.lirmm.graphik.util.stream.CloseableIterator;
import fr.lirmm.graphik.util.stream.IteratorException;

public class computeArguments {

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
		ArrayList<StructuredArgument> F2 = new ArrayList<StructuredArgument>();
		F2.addAll(F);

		if (!F2.isEmpty()) {
			StructuredArgument a = F2.get(0);

			ArrayList<ArrayList<StructuredArgument>> Temp = new ArrayList<ArrayList<StructuredArgument>>();
			for (ArrayList<StructuredArgument> s : S) {
				ArrayList<StructuredArgument> sTemp = new ArrayList<StructuredArgument>();
				sTemp.addAll(s);
				sTemp.add(a);
				Temp.add(sTemp);
			}

			for (ArrayList<StructuredArgument> s1 : Temp) {
				S.add(s1);
			}
			F2.remove(0);

			AllSubset(S, F2);
		}
	}

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
							(dico.get(a)).add(new StructuredArgument(new ArrayList<StructuredArgument>(), a,
									Boolean.valueOf(true)));
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
//						List T = new ArrayList();
//						for (Atom m : Source) {
//							T.add((List) dico.get(m));
//						}

						List<List<StructuredArgument>> T = new ArrayList<>();
						for (Atom m : Source) {
							T.add(dico.get(m));
						}

						for (List<StructuredArgument> p : cartesianProduct(T)) {
							ArrayList<StructuredArgument> copy = new ArrayList<StructuredArgument>();
							copy.addAll(p);

							boolean contain = false;

							for (StructuredArgument z : dico.get(a)) {
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

	public static ArrayList<StructuredArgument> generateArgs(DefeasibleKB kb) {
		ArrayList<StructuredArgument> result = new ArrayList<>();
		HashMap<Atom, ArrayList<StructuredArgument>> dictionnary = new HashMap<Atom, ArrayList<StructuredArgument>>();

		for (Atom a : kb.gad.getVertices()) {
			recurSiveArgs(a, dictionnary, kb);
		}

		for (Atom a : dictionnary.keySet()) {
			result.addAll(dictionnary.get(a));
		}

		return result;
	}

	// This function is used to remove the premises of argument that are
	// inconsistent
	public static boolean RIncosistent(DefeasibleKB kb) throws AtomSetException {
		boolean result = false;
		for (Predicate s : kb.facts.getPredicates())
			if (s.equals(Predicate.BOTTOM)) {
				result = true;
			}
		return result;
	}

}
