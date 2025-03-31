# HI_MuseumDemo
# PURPOSE AND APPROACH

To help visitors engage critically with the exhibition we manually introduce some artificial inconsistencies for educational purposes. We design these inconsistencies on controversial narratives that could spark debate and critiques from visitors. One painting can exemplify many narratives within an exhibition at the same time, even narratives that might seem in contradiction with each other. For instance, the narrative about painters in the 'Dutch golden age' might seem in contrast with the narrative about Non stereotypical representation of black people, as it is common knowledge that the Dutch empire was engaging in slavery trade. We assume a visitor would find meaningful the exploration of the arguments that support the coexistence of these themes within a painting and that such critical engagement can significantly enhance the educational aspect of the exhibition.
On the backhand, introducing artificial inconsistencies between statements, allows us to identify in an explainable way what paths and triples in the knowledge graph contribute to 'support' -explain- each of the two conflicting statements, allowing for a more detailed and satisfying conversation for the user.

# SCENARIO 
This scenario that we use as example, referes to the painting [King Caspar by Hendrick Heerschop](https://commons.wikimedia.org/wiki/File:Hendrick-Heerschop-Koning-Caspar-1654.-Olieverf-op-paneel.-Berlijn-Staatliche-Museen.jpg)

**U:** Why is this painting here? (Requesting the supporting arguments for the painting's inclusion)

**A:** Because this painting is significant for two of the core narratives around the exhibition: showing paintings from the Dutch Golden Age and showing non stereotypical representation of black people.

**U:** But the Dutch Empire was engaging in colonialism and slavery during the golden age, how can paintings of black people from that era be non stereotypical? (Questioning or attacking one of the curatorial arguments)

**A:** We can see that the painting is indeed from the Golden Age, as it dates 1654 and it is painted by a Dutch author. But it also shows a black person in a non stereotypical way, as the model is representing King Caspar, one of the biblical Magi, and the character is represented in a dignified way, looking proud and self confident. The character is portraied on its own, adding to the narrative of black autonomy. Moreover, the author was influenced by Rembrandt, who, despite being a Golden Age painter, often depicted black individuals with a high degree of realism, capturing their unique personal characteristics.

Would you like to know more about how the character is represented or about the social position of black people in the XVIIcentury?

**U:** How is it possible that the models were black? I thought in the XVII century black people where enslaved... (Questioning or attacking one of the curatorial arguments)

**A:** Not all black people in Amsterdam where slaves, and this is precisely the hidden history this exhibiton would like to tell: Black people were present in seventeenth-century Holland, both in society and in art. This subject has long remained in the shadows, but wrongly so. Rembrandt and many of his contemporaries made magnificent works of art that depict black people. It is interesting to notice that the later stereotypes of black people had not yet become dominant. Painters portrayed individual black models from life, with all their personal characteristics. Furthermore, black people were not always secondary figures in minor roles, but sometimes formed the main subject of the art work. 
U: Oh this is very interesting, I learned something today!

# Curation KG related resources 

In the CKG folder.

* **CKG_DOCUMENTATION**: The documentation of the Curation Knowledge Graph with some SPARQL as example
* **CKG_exampleData**: the RDF in turtle serialization with the Curation Ontology and the Data about our example scenario
* **CKG_Demo**: Image with the schema of the Ontology


# Generating argumentation trees
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
 
