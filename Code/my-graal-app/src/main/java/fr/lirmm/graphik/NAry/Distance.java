package fr.lirmm.graphik.NAry;

import fr.lirmm.graphik.NAry.ArgumentationFramework.StructuredArgument;

public class Distance {
	public StructuredArgument source;
	public StructuredArgument target;
	public int dist;
	
	public Distance(StructuredArgument source, StructuredArgument target, int dist) {
		this.source = source;
		this.target = target;
		this.dist = dist;
	}
	 public String toString() {
		    String result = "(" + this.source + ", " + this.target + ", " + this.dist + ")";
		    return result;
		  }
}
