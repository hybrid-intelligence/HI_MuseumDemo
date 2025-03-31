# HI_MuseumDemo
Repository for the HI project Museum Case demonstrator.

## Generating argumentation trees
  Based on the Curation Knowledge Graph, we generate argumentation trees as an immediate step to have a dialogue between a VR system and a user. The argumentation trees are generated from the Curation KG generated above.

  * **Requirements**:
    - This is a Java implementation: Full java 11 support, java 11 is a requirement.  
    - Install OWL API (Link: https://owlapi.sourceforge.net/)
    - Download and install Eclipse
    - It currently supports: DLGP input that supports Datalog+-, logic programming facts.
   
* **Useage**:
  - The code has been made available to reproduce the results we show in our paper. To make sure that it is possible we would refer to the CODE folder.
  - Perform the following steps:
    + To use, create a location where you store the DLGP. You can store datasets in the created folder.
    + Clone a repository to your local computer using a Github link.
    + Go to the directory where your source code is, i.e., .\HI_MuseumDemo\code
    + To generate argumentation trees, you need to follow the steps:
      
          1. Convert  RDF/XML in Turtle format into DLGP format: you run the command: javac rdfToGLGP.java
      
          2. Generate argumentation from the converted files, you run the following command: javac Experiment1.java 
 
## Curation KG related resources

* **CKG_DOCUMENTATION**: The documentation of the Curation Knowledge Graph with some SPARQL as example
* **CKG_exampleData**: the RDF in turtle serialization with the Curation Ontology and the Data about our example scenario
* **CKG_Demo**: Image with the schema of the Ontology
