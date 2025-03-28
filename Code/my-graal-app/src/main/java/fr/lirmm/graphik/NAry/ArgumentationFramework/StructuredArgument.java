package fr.lirmm.graphik.NAry.ArgumentationFramework;


import java.util.ArrayList;
import fr.lirmm.graphik.graal.api.core.Atom;


public class StructuredArgument {
	public ArrayList<StructuredArgument> body;
	public Atom head;
	public Boolean IsPremise;
	private static int numberArgs = 0;
	//public final int myID;
	public int myID;

	public StructuredArgument() {
		this.body = null;
		this.head = null;
		this.IsPremise = Boolean.valueOf(true);
		this.myID = numberArgs;
		numberArgs += 1;
	}

	public StructuredArgument(ArrayList<StructuredArgument> body, Atom head, Boolean isPremise) {
		this.body = body;
		this.head = head;
		this.IsPremise = isPremise;

		this.myID = numberArgs;
		numberArgs += 1;
	}
	
	public boolean isFact() {
		return body.isEmpty();
	}

	public ArrayList<Atom> getPremises() {
		ArrayList result = new ArrayList();
		if (this.body.isEmpty()) {
			result.add(this.head);
			return result;
		}

		for (StructuredArgument p : this.body) {
			result.addAll(p.getPremises());
		}
		return result;
	}

	public String toString() {
		String result = "a" + this.myID + " : [";
		for (StructuredArgument a : this.body) {
			result = result + "a" + a.myID + " ";
		}
		result = result + "] -> " + this.head;
		return result;
	}

	/*
	 * public String toString() { String result = "A" + this.myID + ": {" +
	 * this.body; //for (Argument a : this.body) // { // result = result + a + " ";
	 * // } result = result + "} -> " + "{" + this.head + "}"; return result; }
	 */

}
