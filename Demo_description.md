## PURPOSE AND APPROACH

To help visitors engage critically with the exhibition we manually introduce some artificial inconsistencies for educational purposes. We design these inconsistencies on controversial narratives that could spark debate and critiques from visitors. One painting can exemplify many narratives within an exhibition at the same time, even narratives that might seem in contradiction with each other. For instance, the narrative about painters in the 'Dutch golden age' might seem in contrast with the narrative about Non stereotypical representation of black people, as it is common knowledge that the Dutch empire was engaging in slavery trade. We assume a visitor would find meaningful the exploration of the arguments that support the coexistence of these themes within a painting and that such critical engagement can significantly enhance the educational aspect of the exhibition.
On the backhand, introducing artificial inconsistencies between statements, allows us to identify in an explainable way what paths and triples in the knowledge graph contribute to 'support' -explain- each of the two conflicting statements, allowing for a more detailed and satisfying conversation for the user.

## SCENARIO 
This scenario that we use as example, referes to the painting [King Caspar by Hendrick Heerschop](https://commons.wikimedia.org/wiki/File:Hendrick-Heerschop-Koning-Caspar-1654.-Olieverf-op-paneel.-Berlijn-Staatliche-Museen.jpg)

**U:** Why is this painting here? (Requesting the supporting arguments for the painting's inclusion)

**A:** Because this painting is significant for two of the core narratives around the exhibition: showing paintings from the Dutch Golden Age and showing non stereotypical representation of black people.

**U:** But the Dutch Empire was engaging in colonialism and slavery during the golden age, how can paintings of black people from that era be non stereotypical? (Questioning or attacking one of the curatorial arguments)

**A:** We can see that the painting is indeed from the Golden Age, as it dates 1654 and it is painted by a Dutch author. But it also shows a black person in a non stereotypical way, as the model is representing King Caspar, one of the biblical Magi, and the character is represented in a dignified way, looking proud and self confident. The character is portraied on its own, adding to the narrative of black autonomy. Moreover, the author was influenced by Rembrandt, who, despite being a Golden Age painter, often depicted black individuals with a high degree of realism, capturing their unique personal characteristics.

Would you like to know more about how the character is represented or about the social position of black people in the XVIIcentury?

**U:** How is it possible that the models were black? I thought in the XVII century black people where enslaved... (Questioning or attacking one of the curatorial arguments)

**A:** Not all black people in Amsterdam where slaves, and this is precisely the hidden history this exhibiton would like to tell: Black people were present in seventeenth-century Holland, both in society and in art. This subject has long remained in the shadows, but wrongly so. Rembrandt and many of his contemporaries made magnificent works of art that depict black people. It is interesting to notice that the later stereotypes of black people had not yet become dominant. Painters portrayed individual black models from life, with all their personal characteristics. Furthermore, black people were not always secondary figures in minor roles, but sometimes formed the main subject of the art work. 
U: Oh this is very interesting, I learned something today!


## FUNCTIONING OF THE SYSTEM

The conversational agent (GPT-4o), understand what painting _this_ refers to and that the user is asking the rationale behind the painting's inclusion in the exhibition. In the CKG, the exhibition is linked to the narratives it wants to highlight through the property *crm:P16_used_specific_object* (narratives are modeled as *crm:E89_Propositional_Object*) and, we can find out what narratives are linked to an object through property *:hasAssociatedHeritageObject* .
As artificial inconsistency, we state that an object can only be representative on one narrative:

```
:CuratorialNarrativeEntity rdf:type owl:Class ;

                           rdfs:subClassOf 
                                         [ rdf:type owl:Restriction ;
					owl:onProperty :hasAssociatedHeritageObject ;
					owl:maxQualifiedCardinality "1"^^xsd:nonNegativeInteger ;
					owl:onClass :HeritageObject
					] .
``` 
We then identify **(HOW?)** arguments that support one statement or the other. For instance:
	Narrative: Painters from the Dutch Golden Age
		Arguments: 
				1. Date of the painting between 1575 and 1675 V
				2. The author is Dutch
				3. Maybe other things about materials and style
	Narrative: Non stereotypical representation of black people
		Arguments: 
				4. The author is black V
				5. The black character in the portrait is represented in an autonomous way V
				6. The black character in the portrait highlights positive attributes such as dignity, strength, and beauty X
				7. The painter was influenced by Rembrandt V

I don't know how to represent some of these constraints, and I don't know if it is needed, as Delaram could just check for these specific constraints via SPARQL queries(?). 
If  For the moment I have written only three (although not sure the shapes are correct. I think they lack specification of the specific individuals)

Number 1

```
ckg:CuratorialNarrativeConstraint3
    a sh:NodeShape ;
    sh:targetClass cgk:CuratorialNarrative ;
    sh:property [
        sh:path co:hasAssociatedHeritageObject ;
        sh:node [
            sh:path crm:P108i_was_produced_by ;
            sh:node [
                sh:path crm:P4_has_Time-span ;
                sh:node [
                    sh:property [
                        sh:path rdfs:label ;
                        sh:datatype xsd:integer ;
                        sh:minInclusive "1575"^^xsd:integer ;
                        sh:maxInclusive "1675"^^xsd:integer ;
                    ] ;
                ] ;
            ] ;
        ] ;
    ] .
```

Number 5 (as checking that there is only one person shown in the painting)

```
ckg:CuratorialNarrativeConstraint1
    a sh:NodeShape ;
    sh:targetClass ckg:CuratorialNarrative ;
    sh:property [
        sh:path co:hasAssociatedHeritageObject ;
        sh:node [
            sh:path crm:P65_shows_visual_item ;
            sh:class crm:E36_Visual_Item ;
            sh:qualifiedValueShape [
                sh:path rdf:type ;
                sh:hasValue  crm:E21_Person ;
            ] ;
            sh:qualifiedMinCount 1 ;
            sh:qualifiedMaxCount 1 ;
            sh:minCount 1 ;
            sh:maxCount 1 ;
        ] ;
    ] .
```

Number  7

```
ckg:CuratorialNarrativeConstraint2
    a sh:NodeShape ;
    sh:targetClass ckg:CuratorialNarrative ;
    sh:property [
        sh:path co:hasAssociatedHeritageObject ;
        sh:node [
            sh:path crm:P108i_was_produced_by ;
            sh:node [
                sh:path crm:P15_was_influenced_by ;
                sh:hasValue ckg:Rembrandt ;
            ] ;
        ] ;
    ] .
```

The argumentation framework highlights which of the facts represented in the knowledge graph support that the heritage object represents one narrative or the other, and extracts them producing an argumentation tree.

Consequently, the rasa environment selects the arguments extracted and selects the corresponding triples in the CKG, to provide a relevant answer to the User.
In particular in the rasa environment, it is possible to query the knowledge graph to select specific natural language descriptions about the painting, the exhibition in general and the specific narratives. Aiding the llm's reasoning.

the relevant fields in the CKG are:
1. Information about the exhibition: 

```
crm:E7_Activity  crm:P67i_is_referred_to_by  crm:E1_Description
crm:E1_Description  crm:P190_has_symbolic_content  "content"^^rdfs:Literal
```

**SPARQL**:

```
PREFIX rdf : <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
PREFIX crm: <http://www.cidoc-crm.org/>
PREFIX : <ontology_prefix>

SELECT ?exhibition ?description
WHERE
{
?exhibition rdf:type crm:E7_Activity;
		crm:P67i_is_referred_to_by ?bnode .
?bnode rdf:type crm:E33_E41_Linguistic_Appellation ;
		crm:P190_has_symbolic_content ?description .
}
```

2. Information about the objects in the painting

```
:HeritageObject  crm:P65_shows_visual_item  crm:E36_Visual_Item
crm:E36_Visual_Item  :hasInterpretation  "content"^^rdfs:Literal
``` 

**SPARQL**:

```
PREFIX rdf : <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
PREFIX crm: <http://www.cidoc-crm.org/>
PREFIX : <ontology_prefix>

SELECT ?visualItem ?interpretation
WHERE
{{
	<{painting_uri}> crm:P65_shows_visual_item ?visualItem .
	?visualItem :hasInterpretation ?interpretation .
}}
```

3. Information about the curatorial narratives

``` 
:CuratorialNarrative  :hasDescription  ''content"^^rdfs:Literal
```

**SPARQL**:

``` 
PREFIX rdf : <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
PREFIX crm: <http://www.cidoc-crm.org/>
PREFIX : <ontology_prefix>

SELECT ?narrative ? description
WHERE
{{
?narrative :hasAssociatedHeritageObject <{painting_uri}> ;
		:hasDescription ?description .
}}
```
