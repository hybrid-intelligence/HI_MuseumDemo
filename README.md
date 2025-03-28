# HI_MuseumDemo
Repository for the HI project Museum Case demonstrator.

* **Demo_description**: a document I'm writing to try to make sense of how the system works. You can find in the document:

1. Description of purpose and approach
2. The scenario description
3. Some notes on the CKG part I am not sure about, including additional constraints that I did not yet add to the KG as I don't know if they are needed/can be processed by the Argumentation Framework

    Please feel free to modify and send me feedback or add your own notes for the part that concerns you

* **CKG_DOCUMENTATION**: pretty evidently, the documentation of the Curation Knowledge Graph with some SPARQL as example
* **CKG_exampleData**: the RDF in turtle serialization with the Curation Ontology and the Data about our example scenario
* **CKG_Demo**: Image with the schema of the Ontology

  # Generating argumentation Tree
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
    + Go to the directory where your source code is, i.e., .\SAF-Argumentation\code
    + To generate argumentation trees, you need to follow the steps:
      
          1. Convert  RDF/XML in Turtle format into DLGP format: you run the command: javac rdfToGLGP.java
      
          2. Generate argumentation from the converted files, you run the following command: javac Experiment1.java 
 
  
  
  
