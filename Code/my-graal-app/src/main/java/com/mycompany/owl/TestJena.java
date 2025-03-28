package com.mycompany.owl;

import java.io.InputStream;
import java.sql.PreparedStatement;
import java.util.ArrayList;



import org.apache.jena.ontology.Individual;
import org.apache.jena.ontology.OntClass;
import org.apache.jena.ontology.OntModel;
import org.apache.jena.ontology.OntModelSpec;
import org.apache.jena.rdf.model.ModelFactory;
import org.apache.jena.rdf.model.Property;
import org.apache.jena.rdf.model.RDFNode;
import org.apache.jena.rdf.model.Resource;
import org.apache.jena.rdf.model.Statement;
import org.apache.jena.rdf.model.StmtIterator;
import org.apache.jena.util.FileManager;
import org.apache.jena.util.iterator.ExtendedIterator;

public class TestJena {

	public static void main(String[] args) {
		// TODO Auto-generated method stub
		InputStream ontInputStream = FileManager.get().open("BioGraph.owl");
		if (ontInputStream == null) {
			System.out.println("No input file Found");
		} else {
			ontInputStream = FileManager.get().open("BioGraph.owl");
			OntModel onto = ModelFactory.createOntologyModel(OntModelSpec.OWL_MEM);
			onto.read(ontInputStream,"OWL");
			// onto.write(System.out);
			
			// get indiviual
		//	ArrayList<Resource> results = new ArrayList<Resource>(); 

		//	ExtendedIterator  individuals = onto.listIndividuals();
		//	while (individuals.hasNext()) {
		//		Resource individual = (Resource) individuals.next();
		//		results.add(individual);
		//	}
		//	System.out.println("\n");

		//	for(int i = 0; i < results.size(); i++)
		//	{
		//		Individual ind = onto.getIndividual(results.get(i).toString());
				// Check whether ind is null.
		//		System.out.println( "ind: "+ind );
				// Iterate over all the statements that have ind as subject.
		//		StmtIterator it = ind.listProperties();
		//		while ( it.hasNext() ) {
		//			System.out.println( it.next() );
		//		}
			
		//	}
			
			// get statement
			// list statement in the Model
		//	StmtIterator iter = onto.listStatements();
			//print out the statement
		//	while (iter.hasNext()) {
		//		Statement stmt = iter.nextStatement(); // get next statement
		//		Resource subject = stmt.getSubject(); // get the subject
		//		Property predicate = stmt.getPredicate(); // get the predicate
		//		RDFNode object = stmt.getObject(); // get the object
		//		System.out.print(subject.toString());
		//		System.out.print(" " + predicate.toString() + " ");
		//		if (object instanceof Resource) {
		//		System.out.print(object.toString());
		//		} else {
				// object is a literal
		//		System.out.print(" \"" + object.toString() + "\"");
		//		}
		//		System.out.println(" .");
				
		//	}
			
			// get class
			
		
			    ExtendedIterator<OntClass> iter = onto.listClasses();

			    while ( iter.hasNext()){
			        System.out.println(iter.next());
			    }
		}
	}
	

}
