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
import java.util.Map.Entry;
import java.util.Set;
import java.util.Stack;
//import fr.lirmm.graphik.NAry.DungAF;
import fr.lirmm.graphik.NAry.ArgumentationFramework.StructuredArgument;
import fr.lirmm.graphik.NAry.ArgumentationFramework.Attack;

import org.apache.commons.lang3.tuple.Pair;
import fr.lirmm.graphik.DEFT.gad.GADEdge;
import fr.lirmm.graphik.DEFT.gad.Derivation;
import fr.lirmm.graphik.DEFT.core.DefeasibleAtom;
import fr.lirmm.graphik.DEFT.core.DefeasibleKB;
import fr.lirmm.graphik.DEFT.core.DefeasibleRule;
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
import fr.lirmm.graphik.NAry.Defeater;
import fr.lirmm.graphik.DEFT.dialectical_tree.ArgumentationFramework;
import fr.lirmm.graphik.DEFT.dialectical_tree.argument_preference.ArgumentPreference;



public class AppInitial {
	//	private static String file = "bio-bench.dlgp";
	//	private static String file = "KB1.dlgp";
	private static String file = "/Users/tho310/Data test/Lum test.dlgp";
	private static boolean haveParameters = true;	
	public static InMemoryAtomSet bottomAtomset = new LinkedListAtomSet();
	public static InMemoryAtomSet equalityAtomset = new LinkedListAtomSet();
	public static ConjunctiveQuery bottomQuery = new DefaultConjunctiveQuery(bottomAtomset, Collections.emptyList());
	public static final int NOT_DEFEAT = 0;
	public static final int BLOCKING_DEFEAT = 1;
	public static final int PROPER_DEFEAT = 2;
	public static AtomSet defeasibleFacts = new LinkedListAtomSet();
	//public static DungAF af;


	//private static String file1 = "Tree.txt";


	public static void main(String[] args) throws HomomorphismFactoryException, RuleApplicationException, IOException
	{
		long startTime = System.nanoTime();

		if ((haveParameters) && (args.length != 0)) {
			file = args[0];
		}
		/*else if (haveParameters) {
			System.out.println("Wrong parameters, please give a DLGP file");
			System.exit(0);
		}*/

		try
		{
			DefeasibleKB kb = new DefeasibleKB(file);
			DefeasibleKB kb1 = new DefeasibleKB(file);
			DefeasibleKB kb2 = new DefeasibleKB();
			AtomSet InitialFacts = new LinkedListAtomSet();	
			//AtomSet defeasibleFacts = new LinkedListAtomSet();	
			RuleSet negativeruleset = new LinkedListRuleSet();
			RuleSet positiveruleset = new LinkedListRuleSet();
			RuleSet rules = new LinkedListRuleSet();
			RuleSet functionalruleset = new LinkedListRuleSet();
			RuleSet ruleset = new LinkedListRuleSet();			
			InitialFacts.addAll(kb.facts);
			defeasibleFacts.addAll(kb.defeasibleAtomSet);
			/*CloseableIterator<Atom> it = (CloseableIterator<Atom>) InitialFacts.iterator();
			while (it.hasNext()) {				
				System.out.println(it.next());
			}*/
			//System.out.println("defeasible atoms");
			CloseableIterator<Atom> de = (CloseableIterator<Atom>) defeasibleFacts.iterator();
			while (de.hasNext()) {
				System.out.println(de.next());
			}

			negativeruleset = kb.negativeConstraintSet;	
			System.out.println(negativeruleset);					

			positiveruleset = kb.rules;
			// get functional rules (equality-EGD) 
			Iterator ck = positiveruleset.iterator();
			while (ck.hasNext()) {
				Rule r1 = (Rule) ck.next();
				if (r1.getHead().iterator().next().getPredicate().equals(Predicate.EQUALITY)) {
					functionalruleset.add(r1);
				}
				else {
					rules.add(r1);
				}

			}

			//System.out.println("functuntioal rule: " +functionalruleset);
			//System.out.println(rules);

			//System.out.println(positiveruleset);
			ruleset.addAll(positiveruleset.iterator());
			ruleset.addAll(negativeruleset.iterator());	
			System.out.println("rule set: " + ruleset);

			// create another KB2 that is used for computing arguments
			CloseableIterator<Atom> it = (CloseableIterator<Atom>) InitialFacts.iterator();
			while (it.hasNext()) {
				Atom a = it.next();				
				kb2.addAtom(a);
			}
			System.out.println(kb2.facts);
			Iterator it2 = positiveruleset.iterator();
			while (it2.hasNext()) {
				Rule r2 = (Rule) it2.next();
				if (!r2.getHead().iterator().next().getPredicate().equals(Predicate.EQUALITY)) {
					kb2.addRule(r2);;
				}

			}
		//	System.out.println("kb2 rules: " + kb2.rules);
			kb2.saturate();

			kb.saturate();
			//kb1.saturateWithNegativeConstraint();
			InMemoryAtomSet saturatedAtom = new LinkedListAtomSet();			
			saturatedAtom.addAll(kb2.facts);


			// Compute a set of arguments.
			ArrayList<StructuredArgument> ListArgument = generateArgs(kb2);
			AtomSet Test;
			for (int i = ListArgument.size() - 1; i >= 0; i--)
			{
				Test = new LinkedListAtomSet();
				for (Atom p : ((StructuredArgument)ListArgument.get(i)).getPremises()) {
					Test.add(p);
				}
				kb2.strictAtomSet = Test;
				kb2.saturate();

				if (RIncosistent(kb2)) {
					ListArgument.remove(i);
				}

			}

			System.out.println(".......List of arguments.......");
			System.out.println();


			for (Object A1 : ListArgument) {
				StructuredArgument A = (StructuredArgument)A1;
				System.out.println(A);// + " get Premises: "+ A.getPremises());
				// check whether the argument is defeasible
				//boolean is = isDefeasible(A);	
				//System.out.println(is);
			}
			/*
			 * Compute all attackers for an argument
			 */

			ArrayList Attacks = new ArrayList();

			/*compute attacks under equality rule*/
			if (!functionalruleset.isEmpty()) {

				for(StructuredArgument a: ListArgument) {
					ArrayList<Atom> supportsA = a.getPremises();
					for (StructuredArgument b : ListArgument){
						Atom conB = b.head;

						// compare conB to supportsA
						ArrayList<StructuredArgument> temp = new ArrayList<StructuredArgument>();
						if (checkInequality(supportsA,conB,functionalruleset) == true) {
							temp.add(b);						
						}
						System.out.println(a);
						// check b co trong cau truc cua mot argument khac ko? - co => ko add, ko =>add
						if (!temp.isEmpty()) {
							Attack add = new Attack(temp, a);						
							if (checkAttacks(Attacks, add) == false) {
								Attacks.add(add);
							}
						}				

					}				

				}

			}


			/* the case of negative rules*/
			ArrayList<AtomSet> repairs = new ArrayList<AtomSet>();
			if(!negativeruleset.isEmpty()) {
				// Step1: Convert LinkedListAtomSet to ArrayList

				// Compute a set of repairs.

				repairs = ComputeAllRepairs(kb1);
				//System.out.println("set of repairs: " +  repairs);

				ArrayList<ArrayList<String>> repairString = new ArrayList();
				Iterator<AtomSet> s = repairs.iterator();
				ArrayList subList = new ArrayList();
				ArrayList<String> tempt = new ArrayList();			
				while(s.hasNext()){
					AtomSet pr = s.next();				
					tempt = AtomSetIntoArrayWithoutArity(pr);				
					repairString.add(tempt);				
				}



				// Convert ArrayList<ArrayList<String>> (repairString) to ArrayList<ArrayList<Atom>> (repairsAtom)
				ArrayList repairsAtom = new ArrayList();
				Iterator localIterator3;
				Iterator localIterator2 = repairString.iterator();
				CloseableIterator T;
				for (int i =0; i < repairString.size(); i++) {
					ArrayList R = (ArrayList) repairString.get(i);
					localIterator3 = R.iterator();
					while(localIterator3.hasNext()) {
						String r = (String)localIterator3.next();
						repairsAtom.add(new ArrayList());
						T = saturatedAtom.iterator();
						while (T.hasNext())
						{
							Atom t = (Atom)T.next();
							if (AtomWithoutArity(t).equals(r)){
								((ArrayList)repairsAtom.get(repairsAtom.size()-1)).add(t);
							}
						}
					} 
				}




				// Step2: Compute a set of arguments apprearing in the repairs.

				HashMap<AtomSet,ArrayList<StructuredArgument>> Arg = new HashMap<AtomSet, ArrayList<StructuredArgument>>();		
				Iterator<AtomSet> localIterator4 = repairs.iterator();				 
				while(localIterator4.hasNext()) {				
					AtomSet r = localIterator4.next();					
					Arg.put(r, new ArrayList<StructuredArgument>());
					Iterator<StructuredArgument> T1 = ListArgument.iterator();
					while (T1.hasNext()) {
						StructuredArgument Ar = (StructuredArgument)T1.next();
						ArrayList<Atom> atom1 = Ar.getPremises();
						Boolean checkAtom = true;
						for (int k=0; k<atom1.size(); k++) {										
							if (!r.contains(atom1.get(k))){
								checkAtom = false;
							}
						}
						if (checkAtom == true) {
							Arg.get(r).add(Ar);
						}
					}

				}	


				//ArrayList Attacks = new ArrayList();
				for (AtomSet As: repairs) {
					ArrayList<StructuredArgument> NotInArg = new ArrayList<StructuredArgument>();
					// Step 4: compute a set of arguments that are not in Arg, and them to NotInArg.
					ArrayList<StructuredArgument> arrayArg = Arg.get(As);
					for (StructuredArgument a : ListArgument) {
						if (!arrayArg.contains(a)) {						
							NotInArg.add(a);
						}
					}

					// Step 5: For each argument that is NotInArg, compute attack relation of arguments
					for (StructuredArgument temp : NotInArg) {					
						StructuredArgument aInTemp = temp;
						ArrayList newS = new ArrayList();
						newS.add(new ArrayList());
						AllSubset(newS, arrayArg); //get(r)
						newS.remove(0);
						for (int i = newS.size() - 1; i >= 0; i--) {					
							ArrayList Concs = new ArrayList();
							for (Object b1 : (ArrayList)newS.get(i)) {
								StructuredArgument b = (StructuredArgument)b1;
								Concs.add(b.head);
							}
							// check whether two arguments are conflict (inconsistent)

							int iter = 0;
							boolean inconsistent = false;
							while ((!inconsistent) && (iter < aInTemp.getPremises().size())){						
								AtomSet u = new LinkedListAtomSet();
								for (Object c1 : Concs) {
									Atom c = (Atom)c1;
									u.add(c);
								}
								u.add((Atom)aInTemp.getPremises().get(iter));

								kb.strictAtomSet = u;
								kb.saturate();							
								InMemoryAtomSet newSaturatedAtoms = new LinkedListAtomSet();
								newSaturatedAtoms.addAll(kb.facts);
								//	System.out.println("set of saturate: " + kb.facts);
								//	System.out.println("set of new saturate: " + newSaturatedAtoms);
								inconsistent = IsInconsistent(newSaturatedAtoms, ruleset);
								//inconsistent = RIncosistent(kb);
								//	System.out.println("inconsistent: " + inconsistent);

								iter++;
							}
							if (!inconsistent) {
								newS.remove(i);
							}						

						}

						ArrayList truth = new ArrayList();
						for (int i = 0; i < newS.size(); i++)
							truth.add(Boolean.valueOf(true));
						for (int i = newS.size() - 1; i >= 1; i--) {
							for (int j = i - 1; j >= 0; j--) {
								if (((ArrayList)newS.get(i)).containsAll((Collection)newS.get(j)))
								{
									truth.set(i, Boolean.valueOf(false));
								}
								else if (((ArrayList)newS.get(j)).containsAll((Collection)newS.get(i)))
								{
									truth.set(j, Boolean.valueOf(false));
								}
							}
						}


						/*for (int i = 0; i< truth.size(); i++) {
						System.out.println("gia tri cua truth:" + truth.get(i));
					}*/

						for (int j = newS.size() - 1; j >= 0; j--) {
							if (!((Boolean)truth.get(j)).booleanValue()) {
								newS.remove(j);
							}
						}

						for (int k = 0; k < newS.size(); k++) {
							Attack toAdd = new Attack((ArrayList)newS.get(k), aInTemp);								
							/*if (!Attacks.contains(toAdd)) {							
							Attacks.add(toAdd);
							System.out.println(Attacks);
						}*/
							//check whether an attack is in the set of attacks
							if (checkAttacks(Attacks, toAdd) == false) {							
								Attacks.add(toAdd);
							}						
						} 



					} 
				}
			}
			//}


			System.out.println("...............");
			Iterator At = Attacks.iterator();
			while(At.hasNext()){
				Attack a = (Attack)((Iterator)At).next();
				System.out.println(a);
			}

			System.out.println("There are " + ListArgument.size() + " arguments and " + Attacks.size() + " attacks."); 

			/* compute stable/ prefered extensions
			 * 
			 */
			HashSet<String> argString = new HashSet<String>();
		//	af = new DungAF();
			/* read arguments from ListArgument (ArrayList<StructuredArgument>) to HashSet<String> */
			for (StructuredArgument a : ListArgument) {				
				String aString = "A" + a.myID;
				System.out.println("arg(" + aString + ").");								
				//af.addArgs(aString);
			}
			//argString = af.getArgs();
			//System.out.println("string of args: " + argString);

			/* read attacks from Attacks (ArrayList<Attack>) to HashSet<String>[] []*/
			HashSet<String[] []> atts = new HashSet<String[] []>();
			for (int i=0; i<Attacks.size(); i++) {
				Attack at = (Attack) Attacks.get(i);				
				String target = "A" + at.target.myID;			
				String source = new String();
				for (StructuredArgument argS : at.source) {
					source = "A" + argS.myID;
				}
				System.out.println("att(" + source + "," + target + ").");
				//af.addAtts(new String[][] {{source, target}});
			}
			/*Compute preferred sematics*/
			HashSet<HashSet<String>> preferredExts = new HashSet<HashSet<String>>();
			//preferredExts = af.getPreferredExts();
			System.out.println("preferred extensions: " + preferredExts);

			/*convert extensions from HashSet<HashSet<String>> to ArrayList<ArrayList<StructuredArgument>>*/

			ArrayList<ArrayList<StructuredArgument>> extensions = new ArrayList<ArrayList<StructuredArgument>>();
			for(HashSet<String> extString : preferredExts) {
				ArrayList<StructuredArgument> ext = new ArrayList<StructuredArgument>();
				for (StructuredArgument arg : ListArgument) {
					String argID = "A" + arg.myID;
					if (extString.contains(argID)) {
						ext.add(arg);
					}

				}
				extensions.add(ext);
			}

			System.out.println("Extension after convert: " );

			for (ArrayList<StructuredArgument> print : extensions) {			
				System.out.println(print);
			}

			/*Get union of extensions for skeptical semantics*/

			ArrayList<StructuredArgument> preferredScepticalExt = new ArrayList<StructuredArgument>();
			preferredScepticalExt = getPreferredScepticalExt(extensions);


			/* if (preferredScepticalExt.isEmpty()) {

		            preferredScepticalExt = new ArrayList<StructuredArgument>(extensions.iterator().next()); // initialize preferredScepticalExt to a random preferredExt;

		            for (ArrayList<StructuredArgument> nextExt : extensions) {
		                preferredScepticalExt.retainAll(nextExt);
		            } // remove everything which isn't in every preferred extension;
		        }*/


			System.out.println("Sceptical extensions: " + preferredScepticalExt);




			/* Compute query answer*/

			//ConjunctiveQuery conQuery = DlgpParser.parseQuery("?(X) :- teach(ann,X).");
			/*ConjunctiveQuery conQuery = DlgpParser.parseQuery("?(X) :- phD(ann), teach(ann,X).");
			InMemoryAtomSet atomSetQ = conQuery.getAtomSet();	
			System.out.println(atomSetQ);

			 LinkedList<Atom> answer = new LinkedList<Atom>();

			 CloseableIteratorWithoutException<Atom> it4 = conQuery.iterator();
			while (it4.hasNext()) {
				Atom atomQ =  it4.next();
				System.out.println(atomQ);
				CloseableIterator<Atom> it3 = saturatedAtom.iterator();
				while (it3.hasNext()) {
					Atom initialAtom = it3.next();										
				//	if ((atomQ.getPredicate().equals(initialAtom.getPredicate())) && (atomQ.getTerm(0).equals(initialAtom.getTerm(0)))){	
				//		answers.add(initialAtom);
						System.out.println("result: " + initialAtom);
					}
				}
			}*/



			ConjunctiveQuery query = DlgpParser.parseQuery("? :- professor(ann).");
			//	ConjunctiveQuery query = DlgpParser.parseQuery("? :- phD(ann), teach(ann,X).");
			//ConjunctiveQuery query = DlgpParser.parseQuery("?(X) :- teach(ann,X).");			


			/*int count = 0;
			ArrayList<Atom> answers = new ArrayList<Atom>();
			answers = getAnswersForQuery(query, saturatedAtom);
			Iterator<Atom> ck1 = answers.iterator();
			//CloseableIterator ck = atomQuery.iterator();
			while (ck1.hasNext()) {
				Atom at = (Atom) ck1.next();
				System.out.println("atom: " + at);
				for (int i=0; i< repairs.size(); i++) {	
					//System.out.println(repairs.get(i));
					if (repairs.get(i).contains(at)) {
						count++;						
					}
				}
			}					

			if (count == 0){
				System.out.println("non-accepted");
			}
			if ((count == repairs.size()) || (count/repairs.size() ==  repairs.size())) {
				System.out.println("sceptical");			
			}
			else
				System.out.println("Creduluous");*/


			/*int result;
			result = CheckingBooleanQuery(query, repairs, saturatedAtom);			
				if (result == 0)
				System.out.println("non-accepted");			
			if (result == 1) 
				System.out.println("sceptical");				
			if (result == 2)			
				System.out.println("Creduluous");*/

			ArrayList<StructuredArgument> argumentForQuery = new ArrayList<StructuredArgument>();
			argumentForQuery = GetArgumentForQuery(query, ListArgument, saturatedAtom);
			System.out.println("Set of Arguments for Query: " + argumentForQuery);

			/* Check credulous, skepcitcal, non-accept for argument*/

			int count = 0;
			for (StructuredArgument arg: argumentForQuery) {
				for (int i=0; i<extensions.size(); i++) {
					if (extensions.get(i).contains(arg)){
						count++;
					}
				}
			}
			if (count == 0){
				System.out.println("non-accepted");
			}
			if ((count == extensions.size()) || (count/extensions.size() ==  extensions.size())) {
				System.out.println("sceptical");			
			}
			else
				System.out.println("Creduluous");






			/* print a set of causes for query*/

			/*	System.out.println(".....set of causes of the query.....");
			for (StructuredArgument argQ : argumentForQuery) {
				if (argQ.body.isEmpty()) {
					System.out.println ("causes: " + argQ.head);
				} else {
					Iterator<StructuredArgument> itArg = argQ.body.listIterator();
					System.out.println("causes of  " + argQ + " : " + itArg.next().head);
				}
			}*/

			System.out.println();


			// Compute a dialectical tree.	
						// create argumentation-based tree for each node

						LinkedList<Defeater> setOfDefeaters = new LinkedList<Defeater>();
						LinkedList setOfAttacks = new LinkedList();
						LinkedList TestSub = new LinkedList();

						/* 
						 * Compute a dialectical tree for all arguments
						 */

						/*	for (int i=0; i< ListArgument.size(); i++) {
							StructuredArgument arg = ListArgument.get(i);*/


						/*
						 * Compute a dialectical tree for a given query
						 */
						ArrayList<ArrayList<StructuredArgument>> extForAcc = new ArrayList<ArrayList<StructuredArgument>>();
						ArrayList<ArrayList<StructuredArgument>> extForNotAcc = new ArrayList<ArrayList<StructuredArgument>>();





					}
					//}


					catch (FileNotFoundException e)
					{
						e.printStackTrace();
					}
					catch (IteratorException e) {
						e.printStackTrace();
					}
					catch (AtomSetException e) {
						e.printStackTrace();
					}
					catch (ChaseException e) {
						e.printStackTrace();
					}
					catch (IOException e) {
						e.printStackTrace();
					}
					catch (HomomorphismException e) {
						e.printStackTrace();
					}
					catch (OWL2ParserException e) {
						e.printStackTrace();
					}

					long endTime = System.nanoTime();
					long duration = endTime - startTime;
					System.out.println(duration / 1000000L + " ms");
				}




				public static void AllSubset(ArrayList<ArrayList<StructuredArgument>> S, ArrayList<StructuredArgument> F)
						throws AtomSetException, ChaseException, HomomorphismException
				{
					ArrayList F2 = new ArrayList();
					F2.addAll(F);

					if (!F2.isEmpty())
					{
						StructuredArgument a = (StructuredArgument)F2.get(0);

						ArrayList Temp = new ArrayList();
						for (ArrayList s : S)
						{
							ArrayList sTemp = new ArrayList();
							sTemp.addAll(s);
							sTemp.add(a);
							Temp.add(sTemp);
						}

						//	for (ArrayList s : Temp)
						for (Object s1 : Temp)
						{
							ArrayList s =(ArrayList)s1;
							S.add(s);
						}
						F2.remove(0);

						AllSubset(S, F2);
					}
				}



				public static void recurSiveArgs(Atom a, HashMap<Atom, ArrayList<StructuredArgument>> dico, DefeasibleKB kb)
				{
					try
					{
						Iterator localIterator2;
						Iterator localIterator1 = kb.gad.getDerivations(a).iterator();
						while (localIterator1.hasNext()) {
							Derivation d = (Derivation)localIterator1.next();
							localIterator2 = d.iterator();
							while(localIterator2.hasNext()) {


								//for (Iterator localIterator1 = kb.gad.getDerivations(a).iterator(); localIterator1.hasNext(); localIterator2.hasNext())
								//{
								//	Derivation d = (Derivation)localIterator1.next();

								//localIterator2 = d.iterator(); continue; 

								GADEdge ge = (GADEdge)localIterator2.next();
								if ((ge.getSources() == null) && (ge.getTarget().equals(a)))
								{
									if (dico.get(a) == null) {
										dico.put(a, new ArrayList());
									}
									boolean contain = false;
									for (Object p1 : (ArrayList)dico.get(a)) {						
										StructuredArgument p = (StructuredArgument)p1;
										if (((p.IsPremise = Boolean.valueOf(true)).booleanValue()) && (p.head.equals(a))) {
											contain = true;
										}
									}
									if (!contain)
										((ArrayList)dico.get(a)).add(new StructuredArgument(new ArrayList(), a, Boolean.valueOf(true)));
								}
								else if (ge.getTarget().equals(a)) {
									ArrayList Source = new ArrayList();

									if (ge.getSources() != null) {
										CloseableIterator so = ge.getSources().iterator();
										while (so.hasNext()) {
											Atom nextOne = (Atom)so.next();
											Source.add(nextOne);
											recurSiveArgs(nextOne, dico, kb);
										}

									}

									if (dico.get(a) == null) {
										dico.put(a, new ArrayList());
									}
									List T = new ArrayList();
									//for (Atom m : Source) {
									for (Object m1 : Source) {
										Atom m = (Atom)m1;
										T.add((List)dico.get(m));
									}
									//for (List p : cartesianProduct(T)) {

									for (Object p1 : cartesianProduct(T)) {
										List p = (List)p1;
										ArrayList copy = new ArrayList();
										copy.addAll(p);

										boolean contain = false;
										//for (StructuredArgument z : (ArrayList)dico.get(a)) {
										for (Object z1 : (ArrayList)dico.get(a)) {
											StructuredArgument z = (StructuredArgument)z1;

											if ((z.body.containsAll(copy)) && (copy.containsAll(z.body)))
											{
												contain = true;
											}
										}

										if (!contain) {
											((ArrayList)dico.get(a)).add(new StructuredArgument(copy, a, Boolean.valueOf(false)));
										}
									}
								}
							}
						}
					}
					catch (IteratorException e)
					{
						e.printStackTrace();
					}
				}

				public static ArrayList<StructuredArgument> generateArgs(DefeasibleKB kb)
				{
					ArrayList result = new ArrayList();
					HashMap dictionnary = new HashMap();

					for (Atom a : kb.gad.getVertices()) {
						recurSiveArgs(a, dictionnary, kb);
					}

					//for (Atom a : dictionnary.keySet()) {
					for (Object a1 : dictionnary.keySet()) {
						Atom a = (Atom)a1;
						result.addAll((Collection)dictionnary.get(a));
					}

					return result;
				}

				public static DefeasibleKB ParseOwlFile(String folderName) throws OWL2ParserException, IOException, AtomSetException {
					DefeasibleKB kb = new DefeasibleKB();

					File folder = new File(folderName);
					File[] listOfFiles = folder.listFiles();

					for (File file : listOfFiles)
					{
						if ((file.isFile()) && (!file.getName().equals(".DS_Store")) && (file.getName().subSequence(file.getName().length() - 3, file.getName().length()).equals("owl"))) {
							System.out.println("--------------" + folderName + file.getName() + "--------------");

							File f = new File(folderName + file.getName());
							OWL2Parser parser = new OWL2Parser(f);

							while (parser.hasNext())
							{
								Object o = parser.next();

								if ((o instanceof Atom)) {
									kb.addAtom((Atom)o);
									System.out.println("it is an atom");
								}
								else if ((o instanceof Rule)) {
									kb.addRule((Rule)o);
									System.out.println("it is a rule");
								}
								else if ((o instanceof AtomSet))
								{
									AtomSet temp = (AtomSet)o;

									CloseableIterator itetemp = temp.iterator();
									while (itetemp.hasNext())
										kb.addAtom((Atom)itetemp.next());
								}
								else
								{
									System.err.println(o);
								}
							}
							parser.close();
						}

					}

					return kb;
				}

				protected static <T> List<List<T>> cartesianProduct(List<List<T>> lists) {
					List resultLists = new ArrayList();
					if (lists.size() == 0) {
						resultLists.add(new ArrayList());
						return resultLists;
					}
					List firstList = (List)lists.get(0);
					List remainingLists = cartesianProduct(lists.subList(1, lists.size()));
					Iterator localIterator1 = firstList.iterator();
					while (localIterator1.hasNext()) {
						Object condition = (Object)localIterator1.next();
						Iterator localIterator2 = remainingLists.iterator(); 

						while(localIterator2.hasNext()) {			
							List remainingList = (List)localIterator2.next();
							ArrayList resultList = new ArrayList();
							resultList.add(condition);
							resultList.addAll(remainingList);
							resultLists.add(resultList);
						}
					}
					return resultLists;
				}

				/*Iterator localIterator2;		
					for (Iterator localIterator1 = firstList.iterator(); localIterator1.hasNext(); 
							localIterator2.hasNext())
					{
						Object condition = (Object)localIterator1.next();
						localIterator2 = remainingLists.iterator(); continue; List remainingList = (List)localIterator2.next();
						ArrayList resultList = new ArrayList();
						resultList.add(condition);
						resultList.addAll(remainingList);
						resultLists.add(resultList);
					}

					return resultLists;
				}*/

				public static ArrayList<AtomSet> ComputeAllRepairs(DefeasibleKB kb)	
						throws AtomSetException, ChaseException, HomomorphismException, OWL2ParserException, IOException
				{
					InMemoryAtomSet atomset = new LinkedListAtomSet();
					RuleSet ruleset = new LinkedListRuleSet();
					RuleSet negativeruleset = new LinkedListRuleSet();
					RuleSet positiveruleset = new LinkedListRuleSet();
					RuleSet rules = new LinkedListRuleSet();
					RuleSet functionalRuleSet = new LinkedListRuleSet();
					ArrayList<AtomSet> S = new ArrayList<AtomSet>();
					ArrayList<AtomSet> repair = new ArrayList<AtomSet>();


					AtomSet InitialFacts = new LinkedListAtomSet();		
					InitialFacts.addAll(kb.facts);
					atomset.addAll(kb.facts);

					kb.saturateWithNegativeConstraint();	

					InMemoryAtomSet saturatedAtom = new LinkedListAtomSet();			
					saturatedAtom.addAll(kb.facts);			

					negativeruleset = kb.negativeConstraintSet;	
					positiveruleset = kb.rules;

					Iterator it = positiveruleset.iterator();
					while (it.hasNext()) {
						Rule r = (Rule) it.next();

						if (r.getHead().iterator().next().getPredicate().equals(Predicate.EQUALITY)) {
							negativeruleset.add(r);
						}
						else {
							rules.add(r);
						}
					}


					ruleset.addAll(positiveruleset.iterator());
					ruleset.addAll(negativeruleset.iterator());	


					//@SuppressWarnings("unchecked")
					//	Chase mychase = new SccChase(ruleset.iterator(), saturatedAtom);
					//	mychase.execute();

					ArrayList IsRepair = null;
					int numberOfRepairs = 0;	
					ArrayList<AtomSet> setOfRepairs = new ArrayList<AtomSet>();
					if (!negativeruleset.iterator().hasNext()) {
						S.add(atomset);
						numberOfRepairs++;
						IsRepair = new ArrayList();
						IsRepair.add(Boolean.valueOf(true));
					}
					else
					{
						S.add(new LinkedListAtomSet());
						AllConsistentSubset(S, atomset, ruleset);
						IsRepair = new ArrayList();
						IsRepair.add(Boolean.valueOf(false));
						for (int i = 1; i < S.size(); i++) {
							IsRepair.add(Boolean.valueOf(true));
						}

						for (int k = 0; k < S.size() - 1; k++) {
							for (int l = k + 1; l < S.size(); l++)
							{
								AtomSet a = (AtomSet)S.get(k);
								AtomSet b = (AtomSet)S.get(l);

								Boolean bIncluded = containsAll(a, b);
								Boolean aIncluded = containsAll(b, a);
								if (aIncluded.booleanValue())
								{
									IsRepair.set(k, Boolean.valueOf(false));
								}
								else if (bIncluded.booleanValue())
									IsRepair.set(l, Boolean.valueOf(false));
							}
						}


						for (int i = 0; i < S.size(); i++) {
							if (((Boolean)IsRepair.get(i)).booleanValue())
								numberOfRepairs++;

						}
					}
					for (int i=0; i < S.size(); i++) {
						if (((Boolean)IsRepair.get(i)).booleanValue()) {
							setOfRepairs.add(S.get(i));
						}
					}
					return setOfRepairs;

				}



				private static void AllConsistentSubset(ArrayList<AtomSet> S, InMemoryAtomSet F, RuleSet ruleset) throws IteratorException, AtomSetException, ChaseException, HomomorphismException{


					//InMemoryAtomSet bottomAtomset = new LinkedListAtomSet();
					bottomAtomset.add(DefaultAtomFactory.instance().getBottom());
					ConjunctiveQuery bottomQuery = new DefaultConjunctiveQuery(bottomAtomset, Collections.emptyList());

					//Atom bot = DefaultAtomFactory.instance().getBottom();
					if (F.iterator().hasNext())
					{
						CloseableIterator iterat = (CloseableIterator) F.iterator();
						Atom a = (Atom)iterat.next();

						ArrayList Temp = new ArrayList();
						for (AtomSet s : S)
						{
							InMemoryAtomSet sTemp = new LinkedListAtomSet();
							InMemoryAtomSet sTemp1 = new LinkedListAtomSet();
							sTemp.addAll(s);
							sTemp.add(a);
							sTemp1.addAll(s);
							sTemp1.add(a);

							//		Chase chase = new SccChase(ruleset.iterator(),sTemp1);
							//		chase.execute();
							Chase mychase = new SccChase(ruleset.iterator(), sTemp1);
							mychase.execute();


							CloseableIterator<Substitution> results = SmartHomomorphism.instance().execute(bottomQuery, sTemp1); // sTemp must be an atom set

							if (!results.hasNext())
							{
								Temp.add(sTemp1);
							}

						}

						for (Object s1 : Temp) {
							AtomSet s = (AtomSet)s1;
							S.add(s);
						}
						InMemoryAtomSet newF = new LinkedListAtomSet();
						while (iterat.hasNext())
							newF.add((Atom)iterat.next());
						AllConsistentSubset(S, newF, ruleset);
					}
				}
				public static ArrayList<String> AtomSetIntoArrayWithoutArity(AtomSet a) throws IteratorException
				{
					ArrayList result = new ArrayList();
					CloseableIterator iter = a.iterator();
					while (iter.hasNext())
						result.add(AtomWithoutArity((Atom)iter.next()));
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
					while (ite.hasNext())
					{
						if (!A.contains((Atom)ite.next())) {
							result = false;
						}
					}

					return result;
				}
				public static boolean IsInconsistent(AtomSet s, RuleSet ruleset) throws HomomorphismException, ChaseException, AtomSetException, IteratorException {
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


				/*
				 * Check equality rules
				 */

				public static boolean equalityCompare(ArrayList<Atom> supportsA, Atom conB, RuleSet functionRules) {

					Set<Predicate> preA = new HashSet<Predicate>();
					for (int i=0; i<supportsA.size(); i++) {
						preA.add(supportsA.get(i).getPredicate());

					}
					for (Rule r : functionRules) {
						Set<Predicate> preR = r.getBody().getPredicates();
						for (int j=0; j<supportsA.size(); j++) {
							Atom ele = supportsA.get(j);
							if ((preR.contains(ele.getPredicate())) & (preR.contains(conB.getPredicate()))) {

								if((ele.getTerm(0).equals(conB.getTerm(0))) & (!ele.getTerm(1).equals(conB.getTerm(1)))) {
									return true;

								}
								// only for Biogaphycal Domain
								String str1 = ele.getTerm(0).toString();
								String str2 = conB.getTerm(0).toString();
								if((str1.substring(0,18).equals(str2.substring(0,18))) & (!ele.getTerm(1).equals(conB.getTerm(1)))) {
									return true;
								}
							}
						}

					}
					return false;

				}

				public static boolean RIncosistent(DefeasibleKB kb)
				{
					boolean result = false;
					try {
						for (Predicate s : kb.facts.getPredicates())
							if (s.equals(Predicate.BOTTOM))
							{
								result = true;
							}
					}
					catch (AtomSetException e)
					{
						e.printStackTrace();
					}
					return result;
				}
				/*Get union of extensions for sceptical semantics*/

				public static ArrayList<StructuredArgument> getPreferredScepticalExt(ArrayList<ArrayList<StructuredArgument>> preferredExts) {
					ArrayList<StructuredArgument> preferredScepticalExt = new ArrayList<StructuredArgument>();

					if (preferredScepticalExt.isEmpty()) {            
						preferredScepticalExt = new ArrayList<StructuredArgument>(preferredExts.iterator().next()); // initialize preferredScepticalExt to a random preferredExt;

						for (ArrayList<StructuredArgument> nextExt : preferredExts) {
							preferredScepticalExt.retainAll(nextExt);
						} // remove everything which isn't in every preferred extension;
					}

					return new ArrayList<StructuredArgument>(preferredScepticalExt);
				}   




				/* check whether an argument is created from assertion without applying rules*/

				public static boolean checkAtomArg(ArrayList<StructuredArgument> A) {
					for (int i=0; i<A.size(); i++) {
						StructuredArgument a = A.get(i);
						if (a.getPremises().equals(a.head)) {
							return true;
						}
					}
					return false ;
				}


				public static LinkedList getRemoves(LinkedList setOfAttackers) {
					LinkedList removes = new LinkedList();
					for (int i=0; i<setOfAttackers.size(); i++) {
						ArrayList<StructuredArgument> A =  (ArrayList<StructuredArgument>) setOfAttackers.get(i);
						ArrayList<Atom> atomA = new ArrayList<Atom>();
						ArrayList<StructuredArgument> bodyA = new ArrayList<StructuredArgument>();
						for (int m =0; m < A.size(); m++) {
							StructuredArgument a = A.get(m);
							atomA.addAll(A.get(m).getPremises());
							bodyA.addAll(a.body);
						}

						for (int j = i+1; j<setOfAttackers.size(); j++) {
							ArrayList<StructuredArgument> B = (ArrayList<StructuredArgument>)setOfAttackers.get(j);
							if(!A.equals(B)) {
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
								if ((bodyB.containsAll(bodyA)) && (atomB.containsAll(atomA)) ){
									removes.add(setOfAttackers.get(i));
								}
							}					
						}
					}
					return removes;

				}



				public static LinkedList<StructuredArgument> getAttackersFor(StructuredArgument arg, ArrayList SetOfAttacks, ArrayList<StructuredArgument>ListOfArguments) {	

					Iterator iter = SetOfAttacks.iterator();
					LinkedList AttackersFor = new LinkedList();	
					LinkedList removes = new LinkedList();
					if (SetOfAttacks.isEmpty() ) {
						return null;
					}	

					while (iter.hasNext()){
						Attack at = (Attack) iter.next();										
						if (at.target.equals(arg)) {					
							AttackersFor.add(at.source);				
						}
					}
					/* remove sub-arguments
					 * 1. compute a set of sub-arguments needed to remove
					 * 2. 
					 * */
					removes = getRemoves(AttackersFor);
					LinkedList temp = AttackersFor;
					for (int i=0; i<removes.size(); i++) {
						temp.remove(removes.get(i));
					}
					AttackersFor = temp;
					return AttackersFor;
				}


				/*public LinkedList<Defeater> getDefeatersFor(StructuredArgument arg) throws AtomSetException, HomomorphismException, HomomorphismFactoryException, RuleApplicationException, ChaseException, IteratorException {
					LinkedList<Defeater> defeaters = new LinkedList<Defeater>();

					LinkedList<StructuredArgument> attackers = this.getAttackersFor(arg);

					for(StructuredArgument attacker : attackers) {
						int attackStatus = this.preferenceFunction.compare(attacker, arg);
						if(attackStatus != ArgumentPreference.NOT_DEFEAT) { // NOT_DEFEAT = 0
							defeaters.add(new Defeater(attacker, attackStatus));
						}
					}

					return defeaters;
				}*/


				public static LinkedList<Defeater> getDefeatersFor(StructuredArgument arg, ArrayList SetOfAttacks, ArrayList<StructuredArgument>ListOfArguments) throws AtomSetException, HomomorphismException, HomomorphismFactoryException, RuleApplicationException, ChaseException, IteratorException {
					LinkedList<Defeater> defeaters = new LinkedList<Defeater>();
					LinkedList<StructuredArgument> attackers = getAttackersFor(arg, SetOfAttacks, ListOfArguments);

					Iterator it = attackers.iterator();
					while (it.hasNext()) {
						ArrayList tempAttackers = new ArrayList();
						tempAttackers = (ArrayList) it.next();
						for (int i=0; i<tempAttackers.size(); i++) {
							StructuredArgument attacker = (StructuredArgument) tempAttackers.get(i);
							int attackStatus = compare(attacker,arg);				
							if(attackStatus != 0) {
								defeaters.add(new Defeater(attacker, attackStatus));
							}
						}
					}

					return defeaters;
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

			public static int compare(StructuredArgument attacker, StructuredArgument attackee) throws IteratorException {

				if (isDefeasible(attackee) == false && isDefeasible(attacker) == false) {
					return 2;
				}	

				if(isDefeasible(attackee) == false) {
					return 0; 		
				}

				// else, if the attacker is strict then it wins
				if(isDefeasible(attacker) == false) {
					return 1;
					//return 2;
				}
				// else, the attacker and attackee are both defeasible
				else {
					return 2;
					//	return 1;
				}
			}



			/*if(isDefeasible(attackee) == false) {
						return 0;

					}
					// else, if the attacker is strict then it wins
					if(isDefeasible(attacker) == true) {
						return 1; 
					}
					// else, the attacker and attackee are both defeasible
					else {
						return 2;
					}*/

			// if the attackee and the attacker are both strict
//				if (isDefeasible(attackee) == true && isDefeasible(attacker) == true) {
//					return 2;
			//}

			// if the argument being attacked is strict then it is undefeatable.
			//if(isDefeasible(attackee) == false) {
//				return 0;
			//}

			// else, if the attacker is strict then it wins
//				if(isDefeasible(attacker) == false) {
//					return 2;
			// else, the attacker and attackee are both defeasible

//				} else {
//					return 1;
//				}
			public static int CheckingBooleanQuery(ConjunctiveQuery query, ArrayList<AtomSet> setOfRepairs, InMemoryAtomSet saturatedAtom) throws IteratorException, AtomSetException {
				InMemoryAtomSet atomQuery = query.getAtomSet();
				//System.out.println(atomQuery);	
				int count = 0;
				ArrayList<Atom> answers = new ArrayList<Atom>();
				answers = getAnswersForQuery(query, saturatedAtom);
				Iterator<Atom> ck = answers.iterator();
				//CloseableIterator ck = atomQuery.iterator();
				while (ck.hasNext()) {
					Atom at = (Atom) ck.next();
					for (int i=0; i<setOfRepairs.size(); i++) {					
						if (setOfRepairs.get(i).contains(at)) {
							count++;						
						}
					}
				}
				if (count == 0){
					return 0; // non-acception
				}
				if (count == setOfRepairs.size()) {
					return 1;	// sckeptical			
				}
				else
					return 2;  // credulous
			}

			public static ArrayList<Atom> getAnswersForQuery(ConjunctiveQuery query, InMemoryAtomSet saturatedAtom) throws IteratorException{
				ArrayList<Atom> answers = new ArrayList<Atom>();
				CloseableIterator<Atom> it4 = query.iterator();
				while (it4.hasNext()) {
					Atom atomQ = it4.next();				
					CloseableIterator<Atom> it3 = saturatedAtom.iterator();
					while (it3.hasNext()) {
						Atom initialAtom = it3.next();										
						if ((atomQ.getPredicate().equals(initialAtom.getPredicate())) && (atomQ.getTerm(0).equals(initialAtom.getTerm(0)))){	
							answers.add(initialAtom);					
						}
					}
				}
				return answers;
			}

			public static boolean checkInequality(ArrayList<Atom> supportsA, Atom conB, RuleSet functionRules) {

				Set<Predicate> preA = new HashSet<Predicate>();
				for (int i=0; i<supportsA.size(); i++) {
					preA.add(supportsA.get(i).getPredicate());

				}
				for (Rule r : functionRules) {
					Set<Predicate> preR = r.getBody().getPredicates();
					for (int j=0; j<supportsA.size(); j++) {
						Atom ele = supportsA.get(j);
						if ((preR.contains(ele.getPredicate())) & (preR.contains(conB.getPredicate()))) {

							if((ele.getTerm(0).equals(conB.getTerm(0))) & (!ele.getTerm(1).equals(conB.getTerm(1)))) {
								return true;

							}
							// only for Biogaphycal Domain
							String str1 = ele.getTerm(0).toString();
							String str2 = conB.getTerm(0).toString();
							if((str1.substring(0,18).equals(str2.substring(0,18))) & (!ele.getTerm(1).equals(conB.getTerm(1)))) {
								return true;
							}
						}
					}

				}
				return false;

			}

			public static ArrayList<StructuredArgument> GetArgumentForQuery(ConjunctiveQuery query, ArrayList<StructuredArgument> ListArgument, InMemoryAtomSet saturatedAtom) throws IteratorException {
				ArrayList<StructuredArgument> argumentsFor = new ArrayList<StructuredArgument>();
				ArrayList<Atom> answers = new ArrayList<Atom>();
				answers = getAnswersForQuery(query, saturatedAtom);
				//InMemoryAtomSet atomQuery = query.getAtomSet();
				//CloseableIterator ck = query.iterator();
				Iterator<Atom> ck = answers.iterator();
				while (ck.hasNext()) {
					Atom at = (Atom) ck.next();
					for (int i=0; i<ListArgument.size(); i++) {
						StructuredArgument arg = ListArgument.get(i);
						if (arg.head.equals(at)) {
							argumentsFor.add(arg);
						}			

					}
				}
				return argumentsFor;
			}

			public static boolean checkAttacks(ArrayList<Attack> A, Attack b) {
				boolean result = false;

				for (int i=0; i< A.size(); i++) {
					Attack a = A.get(i);		
					//if (((a.target.equals(b.target)) && (a.source.containsAll(b.source))) || ((a.target.equals(b.target) && checkSubArg(a.source, b.source) == true)) {
					//if (a.target.equals(b.target) && checkSubArg(a.source, b.source) == true) {
					if ((a.target.equals(b.target)) && (a.source.containsAll(b.source))){
						result = true;			
					}			
				}
				return result;		

			}	




			}

			
