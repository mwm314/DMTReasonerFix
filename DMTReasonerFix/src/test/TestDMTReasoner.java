package test;

import static org.junit.Assert.*;

import java.io.File;
import java.util.HashSet;
import java.util.Set;

import main.DMTReasonerFactory;

import org.junit.Test;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.reasoner.Node;
import org.semanticweb.owlapi.reasoner.NodeSet;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.reasoner.impl.OWLClassNodeSet;

import uk.ac.manchester.cs.owl.owlapi.OWLClassImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLObjectIntersectionOfImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLObjectUnionOfImpl;

/**
 * Class to test the DMTreasoner
 * 
 * @author Matt
 *
 */
public class TestDMTReasoner {
	
	private OWLOntologyManager ontManager = OWLManager.createOWLOntologyManager();
	
	/**
	 * Edit this to point to where the ontologies are stored on your local machine.
	 * I'm not fancy/determined enough to link it to the github repo...
	 */
	private String localDirectoryForOntologies = "C:/Users/Matt/Desktop/FinalOntology/";

	@Test
	/**
	 * Subsumption test
	 * Test to show that father subsumes grandfather in the evenMoreComplexParent.owl ontology
	 * Also shows that the DAG builds properly and that the getSubclasses() method function properly for the direct case
	 * @throws Exception
	 */
	public void grandfatherSubClassOfFather() throws Exception {

		//Load .owl file and reason over it
		OWLOntology ont3 = ontManager.loadOntologyFromOntologyDocument(new File(localDirectoryForOntologies + "evenMoreComplexParent.owl"));
		OWLReasoner reasoner = new DMTReasonerFactory().createReasoner(ont3);

		HashSet<OWLClass> classes = new HashSet<>();

		OWLClass father = null;
		OWLClass grandfather = null;

		Set<OWLAxiom> axioms = ont3.getAxioms();
		for (OWLAxiom a : axioms) {
			classes.addAll(a.getClassesInSignature());
		}

		//Grab the father and grandfather classes
		for (OWLClass c : classes) {
			if (c.getIRI().toString().endsWith("Father")) {
				father = new OWLClassImpl(c.getIRI());
			}
			if (c.getIRI().toString().endsWith("Grandfather")) {
				grandfather = new OWLClassImpl(c.getIRI());
			}
		}

		//If we didn't grab them, fail the test
		if (father == null || grandfather == null) {
			assertEquals("Father is null", 0, 1);
		}

		NodeSet<OWLClass> directSubclasses = reasoner.getSubClasses(father, true);
		System.out.println("Node set:" + directSubclasses);

		//See if grandfather is the one and only class
		if (directSubclasses.isSingleton()) {
			for (Node<OWLClass> n : directSubclasses) {
				System.out.println("Node entities: " + n.getEntities());
				if (n.contains(grandfather)) {
					assertEquals(0, 0);
					return;
				}
			}
		}
		
		//If it is not, fail the test
		assertEquals(10, 11);

	}
	
	@Test
	/**
	 * Here we test whether A ^ -A is unsatisfiable
	 */
	public void testClassicUnsatisfiability() throws Exception {
		//Load .owl file and reason over it
		OWLOntology ont3 = ontManager.loadOntologyFromOntologyDocument(new File(localDirectoryForOntologies + "evenMoreComplexParent.owl"));
		OWLReasoner reasoner = new DMTReasonerFactory().createReasoner(ont3);
		
		HashSet<OWLClassExpression> aIntersectNota = new HashSet<OWLClassExpression>();
		OWLClass a = new OWLClassImpl(IRI.create("A"));
		OWLClassExpression notA = a.getComplementNNF();
		
		aIntersectNota.add(a);
		aIntersectNota.add(notA);
		
		assertFalse("A ^ -A is unsatisfiale", reasoner.isSatisfiable(new OWLObjectIntersectionOfImpl(aIntersectNota)));
	}
	
	@Test
	/**
	 * Here we test whether A union -A is satisfiable
	 */
	public void testClassicSatisfiability() throws Exception {
		//Load .owl file and reason over it
		OWLOntology ont3 = ontManager.loadOntologyFromOntologyDocument(new File(localDirectoryForOntologies + "evenMoreComplexParent.owl"));
		OWLReasoner reasoner = new DMTReasonerFactory().createReasoner(ont3);
		
		HashSet<OWLClassExpression> aIntersectNota = new HashSet<OWLClassExpression>();
		OWLClass a = new OWLClassImpl(IRI.create("A"));
		OWLClassExpression notA = a.getComplementNNF();
		
		aIntersectNota.add(a);
		aIntersectNota.add(notA);
		
		assertTrue("A union -A is unsatisfiale", reasoner.isSatisfiable(new OWLObjectUnionOfImpl(aIntersectNota)));
	}
	
	//@Test
	//This one infinite loops for now
	/**
	 * In this case, we want to test some completeness of unions.
	 * We have a class Parent defined as (hasChild some Person), subclass of Person.
	 * We have a class NoChildren defined as (hasChild max 0 Person), subclass of Person.
	 * We should see Person become equivalent to owl:Thing,
	 * because if you have a child, you are a Person. But if you don't have a child, you are also a Person.
	 * Thus, everything is a person.
	 */
	public void testHasChildMaxCard() throws Exception {
		OWLOntology ont3 = ontManager.loadOntologyFromOntologyDocument(new File(localDirectoryForOntologies + "moreComplexParentWithequivalentClasses.owl"));
		OWLReasoner reasoner = new DMTReasonerFactory().createReasoner(ont3);
		
		Node<OWLClass> topNode = reasoner.getTopClassNode();
		
		HashSet<OWLClass> classes = new HashSet<>();

		OWLClass person = null;

		Set<OWLAxiom> axioms = ont3.getAxioms();
		for (OWLAxiom a : axioms) {
			classes.addAll(a.getClassesInSignature());
		}

		//Grab the Person class
		for (OWLClass c : classes) {
			if (c.getIRI().toString().endsWith("Person")) {
				person = new OWLClassImpl(c.getIRI());
			}
		}
		
		//Check it is in the right spot in the DAG
		assertTrue(topNode.contains(person));
	}
	
	//@Test
	//This overflows the stack, infinite recursion issue
	/**
	 * Here we have a class UnsatisfiableMother, which, as you might have guessed, is unsatisfiable.
	 * The definition is (hasChild max 0 Person) and Mother
	 * But Mother is a subclass of Parent, which necessarily have children.
	 * Thus, UnsatisfiableMother is indeed unsatisfiable
	 * @throws Exception
	 */
	public void testUnsatisfiableClass() throws Exception {
		OWLOntology ont3 = ontManager.loadOntologyFromOntologyDocument(new File(localDirectoryForOntologies + "correctDefsCardinalityAndEquivalency.owl"));
		OWLReasoner reasoner = new DMTReasonerFactory().createReasoner(ont3);
		
		Node<OWLClass> bottomNode = reasoner.getBottomClassNode();
		
		HashSet<OWLClass> classes = new HashSet<>();

		OWLClass unsatMother = null;

		Set<OWLAxiom> axioms = ont3.getAxioms();
		for (OWLAxiom a : axioms) {
			classes.addAll(a.getClassesInSignature());
		}

		//Grab the unsatMother class
		for (OWLClass c : classes) {
			if (c.getIRI().toString().endsWith("leMother")) {
				unsatMother = new OWLClassImpl(c.getIRI());
			}
		}
		
		//Check it is in the right spot in the DAG
		assertTrue(bottomNode.contains(unsatMother));
	}
	
	//@Test
	//This also causes an infinite loop, so unions are likely not the issue
	/**
	 * This is really just to see if unions were contributing to the problem of the previous method
	 * @throws Exception
	 */
	public void testUnsatisfiableClassNoUnion() throws Exception {
		OWLOntology ont3 = ontManager.loadOntologyFromOntologyDocument(new File(localDirectoryForOntologies + "noUnion.owl"));
		OWLReasoner reasoner = new DMTReasonerFactory().createReasoner(ont3);
		
		Node<OWLClass> bottomNode = reasoner.getBottomClassNode();
		
		HashSet<OWLClass> classes = new HashSet<>();

		OWLClass unsatMother = null;

		Set<OWLAxiom> axioms = ont3.getAxioms();
		for (OWLAxiom a : axioms) {
			classes.addAll(a.getClassesInSignature());
		}

		//Grab the unsatMother class
		for (OWLClass c : classes) {
			if (c.getIRI().toString().endsWith("leMother")) {
				unsatMother = new OWLClassImpl(c.getIRI());
			}
		}
		
		//Check it is in the right spot in the DAG
		assertTrue(bottomNode.contains(unsatMother));
	}
}
