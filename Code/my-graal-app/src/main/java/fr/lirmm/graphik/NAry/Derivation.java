package fr.lirmm.graphik.NAry;

import java.util.ArrayList;

public class Derivation {
	public ArrayList<String> Body;
	  public String Head;

	  public Derivation()
	  {
	    this.Body = new ArrayList();
	    this.Head = "";
	  }

	  public Derivation(ArrayList<String> body, String head)
	  {
	    this.Body = body;
	    this.Head = head;
	  }
}
