package fr.lirmm.graphik.NAry.ArgumentationFramework;

import java.util.ArrayList;

import org.tweetyproject.graphs.Node;

import fr.lirmm.graphik.graal.api.core.Atom;


public class ArgumentNode extends StructuredArgument implements Node {

	private StructuredArgument argument; // The argument associated with this node
	private ArrayList<ArgumentNode> children; // List of child nodes
	private static int idCounter = 0; // Static counter for auto-incremented node IDs
	private int nodeID; // Unique ID for each ArgumentNode
	//private int level;

	// Constructor that accepts an Argument
	public ArgumentNode(StructuredArgument argument) {
		this.argument = argument; // Assign the provided argument to the node
		this.children = new ArrayList<>(); // Initialize the children list
		this.nodeID = idCounter++; // Assign a unique ID and increment the counter
	}

	// Method to add a child node
	public void addChild(ArgumentNode childNode) {
		children.add(childNode); // Add the child node to the list
	}
	
	// Set the level of node
	//public void setLevel(int l) {
	//	this.level = l;
	//}
	

    // Getter for the unique node ID
    public int getNodeID() {
        return nodeID;
    }

	// Getters for the argument properties
	public ArrayList<StructuredArgument> getBody() {
		return argument.body; // Get the body of the argument
	}

	public ArrayList<Atom> getPremises() {
		ArrayList<Atom> result = new ArrayList();
		if (this.argument.body.isEmpty()) {
			result.add(this.argument.head);
			return result;
		}

		for (StructuredArgument p : this.argument.body) {
			result.addAll(p.getPremises());
		}
		return result;
	}

	public Atom getHead() {
		return argument.head; // Get the head of the argument
	}

	public Boolean isPremise() {
		return argument.IsPremise; // Get the premise status
	}

	public int getArgID() {
		return argument.myID; // Get the unique ID of the argument
	}

	public ArrayList<ArgumentNode> getChildren() {
		return children; // Return the list of child nodes
	}
	

	@Override
	public String toString() {

		String result = "a" + getArgID() + " : [";
		for (StructuredArgument a : this.argument.body) {
			result = result + "a" + a.myID + " ";
		}
		result = result + "] -> " + getHead();
		return result;
	}
}
