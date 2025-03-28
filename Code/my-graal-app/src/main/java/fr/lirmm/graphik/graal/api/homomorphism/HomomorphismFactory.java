package fr.lirmm.graphik.graal.api.homomorphism;

import fr.lirmm.graphik.graal.api.core.AtomSet;
import fr.lirmm.graphik.graal.api.core.Query;

public abstract interface HomomorphismFactory
{
  public abstract Homomorphism getConjunctiveQuerySolver(AtomSet paramAtomSet);

  public abstract Homomorphism getSolver(Query paramQuery, AtomSet paramAtomSet);
}