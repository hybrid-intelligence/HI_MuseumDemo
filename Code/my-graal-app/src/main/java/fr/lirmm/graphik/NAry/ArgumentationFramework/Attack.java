package fr.lirmm.graphik.NAry.ArgumentationFramework;

import java.util.ArrayList;
import java.util.Objects;

public class Attack {
	public ArrayList<StructuredArgument> source;
	public StructuredArgument target;


	public Attack() {
		this.source = null;
		this.target = null;
	}

	public Attack(ArrayList<StructuredArgument> source, StructuredArgument target) {
		this.source = source;
		this.target = target;
	}
	
	 @Override
	    public boolean equals(Object o) {
	        if (this == o) return true;
	        if (!(o instanceof Attack)) return false;
	        Attack attack = (Attack) o;
	        return Objects.equals(this.source, attack.source) && Objects.equals(this.target, attack.target);
	    }

	    @Override
	    public int hashCode() {
	        return Objects.hash(this.source, this.target);
	    }

	public String toString() {
		String result = "({";
		for (StructuredArgument a : this.source) {
			result = result + "a" + a.myID + " ";
		}
		result = result + "}, a" + this.target.myID + ")";
		return result;
	}

}
