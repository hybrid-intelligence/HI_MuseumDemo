package fr.lirmm.graphik.NAry;

import fr.lirmm.graphik.graal.api.core.Atom;

public class PreferenceAtom {
	public Atom atom;
	public int preference;
	PreferenceAtom (Atom atom, int preference) {
		this.atom = atom;
		this.preference = preference;
	}
	
	 public String toString() {
		    String result = "(" + this.atom + ", " + this.preference + ")";
		    return result;
		  }
	 public Atom getAtom() {
		 return this.atom;
	 }
	 public int getPreference () {
		 return this.preference;
	 }
	

}
