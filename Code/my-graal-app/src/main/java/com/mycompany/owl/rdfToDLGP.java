package com.mycompany.owl;

import java.io.IOException;
import java.io.InputStream;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Set;

import org.apache.commons.compress.utils.FileNameUtils;
import org.apache.jena.rdf.model.Model;
import org.apache.jena.rdf.model.ModelFactory;
import org.apache.jena.rdf.model.Property;
import org.apache.jena.rdf.model.RDFNode;
import org.apache.jena.rdf.model.Resource;
import org.apache.jena.rdf.model.Statement;
import org.apache.jena.rdf.model.StmtIterator;
import org.apache.jena.util.FileManager;
import org.apache.jena.vocabulary.RDF;
import org.semanticweb.owlapi.model.OWLNamedObject;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;

import fr.lirmm.graphik.NAry.App1;
import fr.lirmm.graphik.graal.api.core.Atom;
import fr.lirmm.graphik.graal.api.core.AtomSet;
import fr.lirmm.graphik.graal.api.core.AtomSetException;
import fr.lirmm.graphik.graal.api.core.Predicate;
import fr.lirmm.graphik.graal.api.core.Term;
import fr.lirmm.graphik.graal.api.kb.KnowledgeBaseException;
import fr.lirmm.graphik.graal.core.DefaultAtom;
import fr.lirmm.graphik.graal.core.atomset.LinkedListAtomSet;
import fr.lirmm.graphik.graal.core.term.DefaultTermFactory;
import fr.lirmm.graphik.graal.kb.KBBuilderException;

@SuppressWarnings("deprecation")
public class rdfToDLGP {
	static final String inputFileName = "C:/Users/tho310/Data test/Museum Case/CKG-data.rdf";
	// public static Term termSubject
	// public static Term termSubject;

	public static DefaultAtom atom;

	public static void main(String[] args) throws OWLOntologyCreationException, IOException, AtomSetException,
			KBBuilderException, KnowledgeBaseException {
		// load rdf/xml file using Jena.

		// Create an empty model
		Model model = ModelFactory.createDefaultModel();

		InputStream in = FileManager.get().open(inputFileName);

		if (in == null) {
			throw new IllegalArgumentException("File: " + inputFileName + " not found");
		}

		// Read a RDF/XML file
		String extension = FileNameUtils.getExtension(inputFileName);
		if (extension.equals("nt")) {
			model.read(in, null, "N-TRIPLES");
		}
		if (extension.equals("rdf")) {
			model.read(in, "");
		}

		// List all statements in rdf
//		StmtIterator it = model.listStatements(null, RDF.type, (RDFNode) null);
//		if (it.hasNext()) {
//			System.out.println("rdf:type " + it.next());
//		}

		StmtIterator iter = model.listStatements();

		// Transfer from statement to atom
		ArrayList<Atom> atomSet = new ArrayList<>();
		
		while (iter.hasNext()) {
			Statement stmt = iter.nextStatement();
			Resource subject = stmt.getSubject();
			Property predicate = stmt.getPredicate();
			RDFNode object = stmt.getObject();
			Term termObject = null;
			Term termSubject = null;

			// Consider subject as term 0
			if (subject.isAnon()) {
				 continue;
			} else {

				if (predicate.getURI().compareTo("http://www.w3.org/1999/02/22-rdf-syntax-ns#type") == 0) {
					Predicate predicate1 = new Predicate("<" + object.asResource() + ">", 1);
					if (subject.isResource()) {
						termSubject = DefaultTermFactory.instance().createConstant("<" + subject + ">");
					}
					Atom a = new DefaultAtom(predicate1, termSubject);
					atomSet.add(a);
				} else {
					Predicate predicate2 = new Predicate("<" + predicate + ">", 2);
					if (subject.isResource()) {
						termSubject = DefaultTermFactory.instance().createConstant("<" + subject + ">");
					}

					// Consider Object as Term 1

					// Case1 : Objects are literal
					if (object.isLiteral()) {
						termObject = DefaultTermFactory.instance().createLiteral(object.toString());
					}
					// Case2: Objects are resource
					if (object.isResource()) {
						if (object.asResource().getLocalName() == null) {
							termObject = DefaultTermFactory.instance().createConstant("<" + object.asResource() + ">");
						}

					}
					Atom a = new DefaultAtom(predicate2, termSubject, termObject);
					if (a != null || !atomSet.contains(a)) {
						atomSet.add(a);
					} 
				}

			}
		}
		System.out.println("DONE!");

		PrintWriter out = new PrintWriter("/Users/tho310/Data test/Museum Case/test.dlgp");
		for (Atom at : atomSet) {
			out.println(App1.AtomWithoutArity(at) + ".");
		}
		out.close();
	}

	public static Predicate valueToPredicate(Property predicate) {
		return new Predicate(predicate.getLocalName(), 2);
	}

	public static Term objectToTerm(RDFNode object) {
		return null;

	}

	public static String handleIRI(OWLNamedObject obj) {
		if ((obj.getIRI().getFragment() != null)) {
			return obj.getIRI().getFragment().toString();
		}
		return obj.toString();
	}

}
