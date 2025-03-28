package fr.lirmm.graphik.NAry;


import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import fr.lirmm.graphik.NAry.ArgumentationFramework.StructuredArgument;

//import cern.colt.list.BooleanArrayList;

import java.util.HashSet;


public class Graph {
	private Map<StructuredArgument, ArrayList<StructuredArgument>> adjacencyList;

	public Graph() {
		adjacencyList = new HashMap<>();
	}

	public void addEdge(StructuredArgument source, ArrayList<StructuredArgument> destination) {
		adjacencyList.computeIfAbsent(source, k -> new ArrayList<>()).addAll(destination);
	}

	public List<List<StructuredArgument>> printAllPathsEven(StructuredArgument start, StructuredArgument end) {
		List<List<StructuredArgument>> paths = new ArrayList<>();
		List<StructuredArgument> path = new ArrayList<>();
		Set<StructuredArgument> visited = new HashSet<>();

		path.add(start);
		visited.add(start);
		dfsEven(start, end, path, visited, paths);
		return paths;
	}

	private void dfsEven(StructuredArgument current, StructuredArgument end, List<StructuredArgument> path, Set<StructuredArgument> visited, List<List<StructuredArgument>> paths) {
		if (current == end) {
			if ((path.size() % 2 == 0)  & (checkUniqueElements(path) == true)) {
				paths.add(new ArrayList<>(path));
			}
		} else {
			ArrayList<StructuredArgument> neighbors = adjacencyList.getOrDefault(current, new ArrayList<>());
			// remove sub-argument in neighbors
			ArrayList<StructuredArgument> Nneighbors = removeSubArgs(neighbors);
			for (StructuredArgument neighbor : Nneighbors) {
				if (!visited.contains(neighbor)) {
					visited.add(neighbor);
					path.add(neighbor);
					dfsEven(neighbor, end, path, visited, paths);
					path.remove(path.size() - 1);
					visited.remove(neighbor);
				}
			}
		}
	}



	public List<List<StructuredArgument>> printAllPathsOdd(StructuredArgument start, StructuredArgument end) {
		List<List<StructuredArgument>> paths = new ArrayList<>();
		List<StructuredArgument> path = new ArrayList<>();
		Set<StructuredArgument> visited = new HashSet<>();

		path.add(start);
		visited.add(start);
		dfsOdd(start, end, path, visited, paths);

		return paths;

	}

	private void dfsOdd(StructuredArgument current, StructuredArgument end, List<StructuredArgument> path, Set<StructuredArgument> visited, List<List<StructuredArgument>> paths) {
		if (current == end) {
			if ((path.size() % 2 != 0) & (checkUniqueElements(path) == true)) {
				if (checkUniqueElements(path) == true) {
					paths.add(new ArrayList<>(path));
				}
			}
		} else {
			ArrayList<StructuredArgument> neighbors = adjacencyList.getOrDefault(current, new ArrayList<>());
			// remove sub-argument in neighbors
			ArrayList<StructuredArgument> Nneighbors = removeSubArgs(neighbors);
			for (StructuredArgument neighbor : Nneighbors) {
				if (!visited.contains(neighbor)) {
					visited.add(neighbor);
					path.add(neighbor);
					dfsOdd(neighbor, end, path, visited, paths);
					path.remove(path.size() - 1);
					visited.remove(neighbor);
				}
			}
		}

	}




	public List<List<StructuredArgument>> printAllPaths(StructuredArgument start, StructuredArgument end) {
		List<List<StructuredArgument>> paths = new ArrayList<>();
		ArrayList<StructuredArgument> path = new ArrayList<>();
		Set<StructuredArgument> visited = new HashSet<>();

		path.add(start);
		visited.add(start);
		dfs(start, end, path, visited, paths);
		return paths;
	}

	private void dfs(StructuredArgument current, StructuredArgument end, List<StructuredArgument> path, Set<StructuredArgument> visited, List<List<StructuredArgument>> paths) {
		if ((current == end)  & (checkUniqueElements(path) == true)) {
			paths.add(new ArrayList<>(path));
		} else {
			ArrayList<StructuredArgument> neighbors = adjacencyList.getOrDefault(current, new ArrayList<>());
			// remove sub-argument in neighbors
			ArrayList<StructuredArgument> Nneighbors = removeSubArgs(neighbors);
			for (StructuredArgument neighbor : Nneighbors) {
				if (!visited.contains(neighbor)) {// || (checkSubArgInList(visited, neighbor) == false)) {
					visited.add(neighbor);
					path.add(neighbor);
					dfs(neighbor, end, path, visited, paths);
					path.remove(path.size() - 1);
					visited.remove(neighbor);
				}
			}
		}
	}


	/* orginal functions
	public void printAllPaths(Argument start, Argument end) {
		ArrayList<Argument> path = new ArrayList<>();
		Set<Argument> visited = new HashSet<>();

		path.add(start);
		visited.add(start);
		dfs(start, end, path, visited);
	}

	private void dfs(Argument current, Argument end, ArrayList<Argument> path, Set<Argument> visited) {
		if (current == end) {		
			printPath(path);
		} else {
			ArrayList<Argument> neighbors = adjacencyList.getOrDefault(current, new ArrayList<>());
			// remove sub-argument in neighbors
			ArrayList<Argument> Nneighbors = removeSubArgs(neighbors);
			for (Argument neighbor : Nneighbors) {
				if (!visited.contains(neighbor)) {// || (checkSubArgInList(visited, neighbor) == false)) {// check whether the neighbor is a sub-argument of each arg in visited
					visited.add(neighbor);
					path.add(neighbor);
					dfs(neighbor, end, path, visited);
					path.remove(path.size() - 1);
					visited.remove(neighbor);
				}
			}
		}
	}*/



	/*	private void printPath(ArrayList<Argument> path) {
		System.out.println("Path: " + path + "size: " + path.size());
	}*/

	private void printPath(List<StructuredArgument> path) {
		StringBuilder s = new StringBuilder();

		s.append(path.get(0).toString());
		s.append(" <= ");
		for (int i =1; i < path.size() - 1; i++) {
			s.append(path.get(i).toString());
			s.append(" <= ");
		}
		s.append(path.get(path.size()-1).toString());			
		System.out.println(s.toString());
	}



	private static boolean checkSubArg(StructuredArgument b, StructuredArgument a) {
		Boolean result = false;

		for (StructuredArgument bBody : b.body) {
			if (bBody.myID == a.myID) {
				result = true;
			}
		}

		return result;
	}

	/*private static boolean checkSubArgInList(Set<Argument> parents, Argument a) {
		Boolean result = false;
		for (Argument b : parents) {
			ArrayList<Argument> bodyB = b.body;
			if (bodyB.contains(a)) {
				continue;

		//	if (b.getPremises().containsAll(a.getPremises())) {
		//		continue;
			} else {
				if (checkSubArg(b, a) ==  true) {
					result = true;
				}
			}
		}
		return result;
	}*/

	private static boolean checkSubArgInList(List<StructuredArgument> parents, StructuredArgument a) {
		Boolean result = false;
		for (StructuredArgument b : parents) {
			//ArrayList<Argument> bodyB = b.body;
			for (StructuredArgument argB : b.body) {
				if (argB.myID == a.myID) {
					result = true;
					break;
				}
			}
		}
	return result;
}


private static ArrayList<StructuredArgument> computeSubArgs (ArrayList<StructuredArgument> inputList, StructuredArgument a) {
	ArrayList<StructuredArgument> subArgs = new ArrayList<>();
	for (StructuredArgument b : inputList) {
		if ((a.head.equals(b.head)) & (a.getPremises().containsAll(b.getPremises()))) {
			//subArgs = null;
			continue;
		} else {
			if (checkSubArg(a, b) ==  true) {
				subArgs.add(b);
			}
		}
	}
	return subArgs;
}


private static ArrayList<StructuredArgument> removeSubArgs (ArrayList<StructuredArgument> inputList) {
	// Create a HashSet to store unique elements
	HashSet<StructuredArgument> uniqueElements = new HashSet<>();

	// Create a new ArrayList to store the result
	ArrayList<StructuredArgument> resultList = new ArrayList<>();

	ArrayList<StructuredArgument> subArgs = new ArrayList<>();

	//compute sub-arguments
	for (StructuredArgument element : inputList) {
		subArgs.addAll(computeSubArgs(inputList, element));
	}

	for (StructuredArgument a : inputList) {
		if (!subArgs.contains(a)) {
			resultList.add(a);
		}
	}

	return resultList;
}

private static boolean checkUniqueElements(List<StructuredArgument> path) {
	List<StructuredArgument> newPath = new ArrayList<>();
	newPath.add(path.get(0));
	for (int i = 1; i < path.size(); i++) {
		if (checkSubArgInList(newPath, path.get(i)) == false) {
			newPath.add(path.get(i));
		}
	}
	if (newPath.size() == path.size()) {
		return true;
	} else 
		return false;
}






}





