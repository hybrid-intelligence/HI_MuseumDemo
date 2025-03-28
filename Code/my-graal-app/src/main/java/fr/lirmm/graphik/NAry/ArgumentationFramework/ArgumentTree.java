package fr.lirmm.graphik.NAry.ArgumentationFramework;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;

import org.tweetyproject.graphs.HyperDirEdge;
import org.tweetyproject.graphs.HyperGraph;
import org.tweetyproject.math.matrix.Matrix;
import org.tweetyproject.graphs.DirHyperGraph;
import org.tweetyproject.graphs.GeneralEdge;

import fr.lirmm.graphik.NAry.ArgumentationFramework.ArgumentNode;

public class ArgumentTree extends HyperGraph<ArgumentNode> {
//	public class ArgumentTree implements DirHyperGraph<ArgumentNode>{

	/** The root node of this tree. */
	private ArgumentNode rootNode;
	private BufferedWriter writer;

	/**
	 * Creates an empty argument tree for the given root node.
	 * 
	 * @param root the root node.
	 */
	public ArgumentTree(ArgumentNode root) {
		super();
		this.rootNode = root;
	}

	/**
	 * Returns the root node of this tree.
	 * 
	 * @return the root node of this tree.
	 */
	public ArgumentNode getRoot() {
		return this.rootNode;
	}

	private Collection<ArgumentNode> getChildren(ArgumentNode node) {
		HashSet<ArgumentNode> result = new HashSet<ArgumentNode>();
		for (HyperDirEdge<ArgumentNode> e : this.edges) {
			if (e.getNodeB().equals(node)) {
				result.addAll(e.getNodeA());
			}
		}
		return result;
	}

	// get height
	public int getHeight() {
		return calculateHeight(this.rootNode);
	}

	private int calculateHeight(ArgumentNode node) {
		if (node == null) {
			return -1; // No height for null nodes
		}

		Collection<ArgumentNode> children = this.getChildren(node);
		if (children == null || children.isEmpty()) {
			return 0; // Leaf node has height 0
		}

		int maxChildHeight = -1;
		for (ArgumentNode child : children) {
			maxChildHeight = Math.max(maxChildHeight, calculateHeight(child));
		}

		return 1 + maxChildHeight;
	}

	// get width

	public int getMaxWidth() {
		return calculateMaxWidth(this.rootNode);
	}

	public int calculateMaxWidth(ArgumentNode root) {
		if (root == null)
			return 0;

		Queue<ArgumentNode> queue = new LinkedList<>();
		queue.add(root);
		int maxWidth = 0;

		while (!queue.isEmpty()) {
			int levelWidth = queue.size();
			// Update the maximum width if the current level width is greater
			if (levelWidth > maxWidth) {
				maxWidth = levelWidth;
			}

			// Process each node at the current level
			for (int i = 0; i < levelWidth; i++) {
				ArgumentNode current = queue.poll();
				Collection<ArgumentNode> children = this.getChildren(current);
				if (children != null) {
					queue.addAll(children);
				}
			}
		}

		return maxWidth;
	}

	/**
	 * Returns a string representation of this argument tree.
	 * 
	 * @return a string representation of this argument tree.
	 */

	/*
	 * public String prettyPrint(){ return this.prettyPrint(this.rootNode, new
	 * HashSet<ArgumentNode>(), 0); }
	 */

	/**
	 * Returns a string representation of the subtree rooted at the given node.
	 * 
	 * @param node         some node.
	 * @param visitedNodes already visited nodes.
	 * @param depth        depth for indentation.
	 * @return a string.
	 */
	// Method to print tree from hypergraph

	// Print the tree from a hypergraph starting from the specified root node

	/*
	 * public void printTree(ArgumentNode root) { printTreeHelper(root, new
	 * HashSet<>(), "", new HashSet<>()); }
	 * 
	 * private void printTreeHelper(ArgumentNode node, Set<ArgumentNode>
	 * currentPath, String indent, Set<HyperDirEdge> visitedEdges) { // Mark the
	 * current node in the current path
	 * 
	 * if (currentPath.contains(node)) { System.out.println(indent + node +
	 * " (cycle detected)"); return; }
	 * 
	 * // Print the node itself System.out.println(indent + node);
	 * currentPath.add(node);
	 * 
	 * // Find all hyperedges where this node is the target
	 * 
	 * for (HyperDirEdge edge : this.getEdges()) {
	 * 
	 * if (edge.getNodeB().equals(node) && !visitedEdges.contains(edge)) {
	 * visitedEdges.add(edge); // Only visit each hyperedge once
	 * 
	 * // Print the attackers in the hyperedge as children for (Object ob :
	 * edge.getNodeA()) { ArgumentNode attacker = (ArgumentNode) ob;
	 * printTreeHelper(attacker, new HashSet<>(currentPath), indent + "   ",
	 * visitedEdges); } } } currentPath.remove(node); // Backtrack for new branches
	 * }
	 */

	// print in a text file

	public void printTree(ArgumentNode root, BufferedWriter writer) throws IOException {
		printTreeHelper(root, new HashSet<>(), "", new HashSet<>(), writer);
		//writer.close(); // Close the writer after the tree is printed
	}

	private void printTreeHelper(ArgumentNode node, Set<ArgumentNode> currentPath, String indent,
			Set<HyperDirEdge> visitedEdges, BufferedWriter writer) throws IOException {
		// Mark the current node in the current path
		if (currentPath.contains(node)) {
			writer.write(indent + node + " (cycle detected)\n");
			return;
		}

		// Write the node itself 
		writer.write(indent + node + "\n");
		currentPath.add(node);

		// Find all hyperedges where this node is the target
		for (HyperDirEdge edge : this.getEdges()) {
			if (edge.getNodeB().equals(node) && !visitedEdges.contains(edge)) {
				visitedEdges.add(edge); // Only visit each hyperedge once

				// Write the attackers in the hyperedge as children
				for (Object ob : edge.getNodeA()) {
					ArgumentNode attacker = (ArgumentNode) ob;
					printTreeHelper(attacker, new HashSet<>(currentPath), indent + "   ", visitedEdges, writer);
				}
			}
		}
		currentPath.remove(node); // Backtrack for new branches
	}

	public String printTreeGUI(ArgumentNode root) {
		StringBuilder result = new StringBuilder();
		printTreeHelperGUI(root, new HashSet<>(), "", new HashSet<>(), result);
		return result.toString();
	}

	private void printTreeHelperGUI(ArgumentNode node, Set<ArgumentNode> currentPath, String indent,
			Set<HyperDirEdge> visitedEdges, StringBuilder result) {
		// Check for cycles in the path
		if (currentPath.contains(node)) {
			result.append(indent).append(node).append(" (cycle detected)\n");
			return;
		}

		// Print the current node
		result.append(indent).append(node).append("\n");
		currentPath.add(node);

		// Process all hyperedges where this node is the target
		for (HyperDirEdge edge : this.getEdges()) {
			if (edge.getNodeB().equals(node) && !visitedEdges.contains(edge)) {
				visitedEdges.add(edge); // Mark this edge as visited

				// Print attackers in the hyperedge as children
				for (Object ob : edge.getNodeA()) {
					ArgumentNode attacker = (ArgumentNode) ob;
					printTreeHelperGUI(attacker, new HashSet<>(currentPath), indent + "   ", visitedEdges, result);
				}
			}
		}

		currentPath.remove(node); // Backtrack to allow new paths
	}

}
