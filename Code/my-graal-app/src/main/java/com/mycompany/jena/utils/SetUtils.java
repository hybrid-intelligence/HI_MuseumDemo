package com.mycompany.jena.utils;


import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

public class SetUtils {
	public static <U> boolean areNullOrEqual(Collection<U> s1, Collection<U> s2)
	  {
	    if ((s1 == null) || (s2 == null)) {
	      return true;
	    }

	    for (Object o : s1) {
	      if (!s2.contains(o)) {
	        return false;
	      }
	    }

	    for (Object o : s2) {
	      if (!s1.contains(o)) {
	        return false;
	      }
	    }

	    return true;
	  }

	  public static <U> boolean areDisjoint(Set<U> s1, Set<U> s2) {
	    for (Object o : s2) {
	      if (s1.contains(o)) {
	        return false;
	      }
	    }

	    return true;
	  }

	  public static <U> Set<Set<U>> mergeSets(Set<Set<U>> sets, Set<U> newSet) {
	    Set res = new HashSet();

	    Set mergedSet = new HashSet();

	    for (Set eSet : sets) {
	      if (!areDisjoint(eSet, newSet))
	        mergedSet.addAll(eSet);
	      else {
	        res.add(eSet);
	      }
	    }

	    mergedSet.addAll(newSet);

	    res.add(mergedSet);

	    return res;
	  }

	  public static <U> Set<U> elementDifference(Collection<U> s1, Collection<U> s2)
	  {
	    Set res = new HashSet();

	    if ((s1 == null) && (s2 == null))
	      return res;
	    if (s1 == null) {
	      res.addAll(s2);
	      return res;
	    }if (s2 == null) {
	      res.addAll(s1);
	      return res;
	    }

	    for (Object o : s1) {
	      if (!s2.contains(o)) {
	        res.add(o);
	      }
	    }

	    for (Object o : s2) {
	      if (!s1.contains(o)) {
	        res.add(o);
	      }
	    }

	    return res;
	  }

	  public static <U> boolean areEqual(Collection<U> s1, Collection<U> s2)
	  {
	    if ((s1 == null) && (s2 == null))
	      return true;
	    if ((s1 == null) || (s2 == null)) {
	      return false;
	    }

	    for (Iterator localIterator = s1.iterator(); localIterator.hasNext(); ) { Object o = localIterator.next();
	      if (!s2.contains(o)) {
	        return false;
	      }
	    }

	    for (Iterator localIterator = s2.iterator(); localIterator.hasNext(); ) { Object o = localIterator.next();
	      if (!s1.contains(o)) {
	        return false;
	      }
	    }

	    return true;
	  }

	  public static <U> Set<U> intersection(Collection<U> s1, Collection<U> s2)
	  {
	    Set res = new HashSet();

	    for (Object o : s1) {
	      if (s2.contains(o)) {
	        res.add(o);
	      }
	    }
	    return res;
	  }

	  public static <U> Set<U> union(Collection<U>[] sets)
	  {
	    Set res = new HashSet();

	    Collection[] arrayOfCollection = sets; int j = sets.length; for (int i = 0; i < j; i++) { Collection s = arrayOfCollection[i];
	      res.addAll(s);
	    }

	    return res;
	  }

	  public static <U> Set<U> difference(Collection<U> s1, Collection<U> s2)
	  {
	    Set res = new HashSet();

	    for (Object o : s1) {
	      if (!s2.contains(o)) {
	        res.add(o);
	      }
	    }

	    return res;
	  }

	  public static Set flatten(Set<?> s)
	  {
	    Set res = new HashSet();

	    for (Iterator localIterator = s.iterator(); localIterator.hasNext(); ) { Object o = localIterator.next();
	      if ((o instanceof Set))
	        res.addAll(flatten((Set)o));
	      else {
	        res.add(o);
	      }
	    }

	    return res;
	  }

	  public static <T> Set<T> objectToSet(T obj)
	  {
	    Set set = new HashSet();
	    set.add(obj);

	    return set;
	  }

	  public static <T> ArrayList<Set<T>> cloneArrayListSet(ArrayList<Set<T>> cover) {
	    ArrayList res = new ArrayList();

	    for (Set s : cover) {
	      res.add((Set)((HashSet)s).clone());
	    }

	    return res;
	  }

}
