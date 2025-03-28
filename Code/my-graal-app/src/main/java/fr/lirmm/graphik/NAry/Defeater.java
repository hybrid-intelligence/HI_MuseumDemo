package fr.lirmm.graphik.NAry;

import fr.lirmm.graphik.NAry.ArgumentationFramework.StructuredArgument;

public class Defeater {
	public StructuredArgument argument;
	public int defeatType;
	
	Defeater(StructuredArgument argument, int defeatType) {
		//Defeater(Argument argument) {
		this.argument = argument;
		this.defeatType = defeatType;
	}

}
