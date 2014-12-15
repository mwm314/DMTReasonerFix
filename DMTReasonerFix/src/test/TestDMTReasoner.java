package test;

import static org.junit.Assert.*;

import java.io.File;
import java.util.HashSet;
import java.util.Set;

import javax.swing.JFrame;

import main.DMTReasoner;
import main.DMTReasonerFactory;

import org.jgrapht.ext.JGraphXAdapter;
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
import org.semanticweb.owlapi.reasoner.impl.OWLClassNode;
import org.semanticweb.owlapi.reasoner.impl.OWLClassNodeSet;

import com.mxgraph.layout.hierarchical.mxHierarchicalLayout;
import com.mxgraph.swing.mxGraphComponent;
import com.mxgraph.view.mxGraph;

import uk.ac.manchester.cs.owl.owlapi.OWLClassImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLObjectIntersectionOfImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLObjectUnionOfImpl;

/**
 * Class to test the DMTreasoner. This class was primarily used to test DAG
 * query methods before the reasoner was implemented
 * 
 * @author Matt
 *
 */
public class TestDMTReasoner {

	private OWLOntologyManager ontManager = OWLManager.createOWLOntologyManager();

	/**
	 * Edit this to point to where the ontologies are stored on your local
	 * machine. I'm not fancy/determined enough to link it to the github repo...
	 */
	// private String localDirectoryForOntologies =
	// "C:\\Users\\Keechwa\\Documents\\GitHub\\DMTReasonerFix\\DMTreasonerFix\\src\\test\\";
	private String localDirectoryForOntologies = "C:/Users/Matt/Desktop/FinalOntology/";

	@Test
	/**
	 * Test whether our DAG is being built correctly in the simple case
	 */
	public void testGetBottomAndGetTopClassNode() throws Exception {
		OWLOntology ont3 = ontManager.loadOntologyFromOntologyDocument(new File(localDirectoryForOntologies + "simpleParent.owl"));
		OWLReasoner reasoner = new DMTReasonerFactory().createReasoner(ont3);

		OWLClass nothing = new OWLClassImpl(IRI.create("owl:Nothing"));
		OWLClass thing = new OWLClassImpl(IRI.create("owl:Thing"));

		assertTrue(reasoner.getBottomClassNode().isBottomNode());
		assertTrue(reasoner.getTopClassNode().isTopNode());
	}

	@Test
	/**
	 * Subsumption test
	 * Test to show that father subsumes grandfather in the evenMoreComplexParent.owl ontology
	 * Also shows that the DAG builds properly and that the getSubclasses() method function properly for the direct case
	 * @throws Exception
	 */
	public void grandfatherSubClassOfFather() throws Exception {

		// Load .owl file and reason over it
		OWLOntology ont3 = ontManager.loadOntologyFromOntologyDocument(new File(localDirectoryForOntologies + "evenMoreComplexParent.owl"));
		OWLReasoner reasoner = new DMTReasonerFactory().createReasoner(ont3);

		HashSet<OWLClass> classes = new HashSet<>();

		OWLClass father = null;
		OWLClass grandfather = null;

		Set<OWLAxiom> axioms = ont3.getAxioms();
		for (OWLAxiom a : axioms) {
			classes.addAll(a.getClassesInSignature());
		}

		// Grab the father and grandfather classes
		for (OWLClass c : classes) {
			if (c.getIRI().toString().endsWith("Father")) {
				father = new OWLClassImpl(c.getIRI());
			}
			if (c.getIRI().toString().endsWith("Grandfather")) {
				grandfather = new OWLClassImpl(c.getIRI());
			}
		}

		// If we didn't grab them, fail the test
		if (father == null || grandfather == null) {
			assertEquals("Father is null", 0, 1);
		}

		NodeSet<OWLClass> directSubclasses = reasoner.getSubClasses(father, true);

		// See if grandfather is the one and only class
		assertTrue(directSubclasses.isSingleton());
		assertTrue(directSubclasses.containsEntity(grandfather));

	}

	@Test
	/**
	 * Test whether we can get all subclasses of the parent class
	 */
	public void allSubclassesOfParent() throws Exception {

		// Load .owl file and reason over it
		OWLOntology ont3 = ontManager.loadOntologyFromOntologyDocument(new File(localDirectoryForOntologies + "evenMoreComplexParent.owl"));
		OWLReasoner reasoner = new DMTReasonerFactory().createReasoner(ont3);

		HashSet<OWLClass> classes = new HashSet<>();

		OWLClass parent = null;
		OWLClass grandparent = null;
		OWLClass grandmother = null;
		OWLClass grandfather = null;
		OWLClass father = null;
		OWLClass mother = null;
		OWLClass nothing = new OWLClassImpl(IRI.create("http://www.w3.org/2002/07/owl#Nothing"));

		Set<OWLAxiom> axioms = ont3.getAxioms();
		for (OWLAxiom a : axioms) {
			classes.addAll(a.getClassesInSignature());
		}

		// Grab the classes we need
		for (OWLClass c : classes) {
			if (c.getIRI().toString().endsWith("Parent")) {
				parent = new OWLClassImpl(c.getIRI());
			}
			if (c.getIRI().toString().endsWith("Grandparent")) {
				grandparent = new OWLClassImpl(c.getIRI());
			}
			if (c.getIRI().toString().endsWith("Grandmother")) {
				grandmother = new OWLClassImpl(c.getIRI());
			}
			if (c.getIRI().toString().endsWith("Grandfather")) {
				grandfather = new OWLClassImpl(c.getIRI());
			}
			if (c.getIRI().toString().endsWith("Father")) {
				father = new OWLClassImpl(c.getIRI());
			}
			if (c.getIRI().toString().endsWith("Mother")) {
				mother = new OWLClassImpl(c.getIRI());
			}
		}

		// If we didn't grab parent, fail the test
		if (parent == null) {
			assertEquals("Parent is null", 0, 1);
		}

		NodeSet<OWLClass> allSubclasses = reasoner.getSubClasses(parent, false);

		assertTrue(allSubclasses.getFlattened().size() == 7);
		assertTrue(allSubclasses.containsEntity(parent));
		assertTrue(allSubclasses.containsEntity(grandparent));
		assertTrue(allSubclasses.containsEntity(grandfather));
		assertTrue(allSubclasses.containsEntity(grandmother));
		assertTrue(allSubclasses.containsEntity(father));
		assertTrue(allSubclasses.containsEntity(mother));
		assertTrue(allSubclasses.containsEntity(nothing));
	}

	@Test
	/**
	 * Now we want to test the other way, to see if father is a super class of grandfather
	 */
	public void fatherSuperclassOfGrandfather() throws Exception {

		// Load .owl file and reason over it
		OWLOntology ont3 = ontManager.loadOntologyFromOntologyDocument(new File(localDirectoryForOntologies + "evenMoreComplexParent.owl"));
		OWLReasoner reasoner = new DMTReasonerFactory().createReasoner(ont3);

		HashSet<OWLClass> classes = new HashSet<>();

		OWLClass father = null;
		OWLClass grandfather = null;

		Set<OWLAxiom> axioms = ont3.getAxioms();
		for (OWLAxiom a : axioms) {
			classes.addAll(a.getClassesInSignature());
		}

		// Grab the father and grandfather classes
		for (OWLClass c : classes) {
			if (c.getIRI().toString().endsWith("Father")) {
				father = new OWLClassImpl(c.getIRI());
			}
			if (c.getIRI().toString().endsWith("Grandfather")) {
				grandfather = new OWLClassImpl(c.getIRI());
			}
		}

		// If we didn't grab them, fail the test
		if (father == null || grandfather == null) {
			assertEquals("Father is null", 0, 1);
		}

		NodeSet<OWLClass> directSubclasses = reasoner.getSuperClasses(grandfather, true);

		// See if father is a superclass of grandfather
		assertTrue(directSubclasses.containsEntity(father));
	}
	
	@Test
	/**
	 * Want to see if we can get all the superclasses of Grandmother.
	 * @throws Exception
	 */
	public void allSuperclassesOfGrandmother() throws Exception {
		// Load .owl file and reason over it
		OWLOntology ont3 = ontManager.loadOntologyFromOntologyDocument(new File(localDirectoryForOntologies + "correctAndFinalParent.owl"));
		OWLReasoner reasoner = new DMTReasonerFactory().createReasoner(ont3);

		HashSet<OWLClass> classes = new HashSet<>();

		OWLClass person = null;
		OWLClass parent = null;
		OWLClass grandparent = null;
		OWLClass grandmother = null;
		OWLClass mother = null;
		OWLClass female = null;
		OWLClass thing = new OWLClassImpl(IRI.create("http://www.w3.org/2002/07/owl#Thing"));

		Set<OWLAxiom> axioms = ont3.getAxioms();
		for (OWLAxiom a : axioms) {
			classes.addAll(a.getClassesInSignature());
		}

		// Grab the classes we need
		for (OWLClass c : classes) {
			if (c.getIRI().toString().endsWith("Parent")) {
				parent = new OWLClassImpl(c.getIRI());
			}
			if (c.getIRI().toString().endsWith("Person")) {
				person = new OWLClassImpl(c.getIRI());
			}
			if (c.getIRI().toString().endsWith("Grandparent")) {
				grandparent = new OWLClassImpl(c.getIRI());
			}
			if (c.getIRI().toString().endsWith("Grandmother")) {
				grandmother = new OWLClassImpl(c.getIRI());
			}
			if (c.getIRI().toString().endsWith("Mother")) {
				mother = new OWLClassImpl(c.getIRI());
			}
			if (c.getIRI().toString().endsWith("Female")) {
				female = new OWLClassImpl(c.getIRI());
			}
		}

		// If we didn't grab parent, fail the test
		if (parent == null) {
			assertEquals("Parent is null", 0, 1);
		}

		//Get all the superclasses of grandmother
		NodeSet<OWLClass> allSuperclasses = reasoner.getSuperClasses(grandmother, false);
		
		System.out.println("ALLSUPP: " + allSuperclasses);

		assertTrue(allSuperclasses.getFlattened().size() == 7);
		assertTrue(allSuperclasses.containsEntity(person));
		assertTrue(allSuperclasses.containsEntity(parent));
		assertTrue(allSuperclasses.containsEntity(grandparent));
		assertTrue(allSuperclasses.containsEntity(grandmother));
		assertTrue(allSuperclasses.containsEntity(mother));
		assertTrue(allSuperclasses.containsEntity(female));
		assertTrue(allSuperclasses.containsEntity(thing));
	}

	@Test
	/**
	 * Here we test whether A ^ -A is unsatisfiable
	 */
	public void testClassicUnsatisfiability() throws Exception {
		// Load .owl file and reason over it
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
	 * Test whether we can get disjoint classes
	 */
	public void testDisjoinClasses() throws Exception {
		// Load .owl file and reason over it
		OWLOntology ont3 = ontManager.loadOntologyFromOntologyDocument(new File(localDirectoryForOntologies + "evenMoreComplexParent.owl"));
		OWLReasoner reasoner = new DMTReasonerFactory().createReasoner(ont3);

		HashSet<OWLClass> classes = new HashSet<>();

		OWLClass male = null;
		OWLClass female = null;

		Set<OWLAxiom> axioms = ont3.getAxioms();
		for (OWLAxiom a : axioms) {
			classes.addAll(a.getClassesInSignature());
		}

		// Grab the classes we need
		for (OWLClass c : classes) {
			if (c.getIRI().toString().endsWith("Male")) {
				male = new OWLClassImpl(c.getIRI());
			}
			if (c.getIRI().toString().endsWith("Female")) {
				female = new OWLClassImpl(c.getIRI());
			}
		}

		// If we didn't grab male/female, fail the test
		if (male == null || female == null) {
			assertEquals("Parent is null", 0, 1);
		}

		OWLClassNodeSet disjointClassesFromMale = (OWLClassNodeSet) reasoner.getDisjointClasses(male);

		// Make sure that male and female are disjoint
		assertTrue(disjointClassesFromMale.containsEntity(female));
	}

	@Test
	/**
	 * Here we test whether A union -A is satisfiable
	 */
	public void testClassicSatisfiability() throws Exception {
		// Load .owl file and reason over it
		OWLOntology ont3 = ontManager.loadOntologyFromOntologyDocument(new File(localDirectoryForOntologies + "evenMoreComplexParent.owl"));
		OWLReasoner reasoner = new DMTReasonerFactory().createReasoner(ont3);

		HashSet<OWLClassExpression> aIntersectNota = new HashSet<OWLClassExpression>();
		OWLClass a = new OWLClassImpl(IRI.create("A"));
		OWLClassExpression notA = a.getComplementNNF();

		aIntersectNota.add(a);
		aIntersectNota.add(notA);

		assertTrue("A union -A is unsatisfiale", reasoner.isSatisfiable(new OWLObjectUnionOfImpl(aIntersectNota)));
	}

	@Test
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

		// Grab the Person class
		for (OWLClass c : classes) {
			if (c.getIRI().toString().endsWith("Person")) {
				person = new OWLClassImpl(c.getIRI());
			}
		}

		// Check it is in the right spot in the DAG
		assertTrue(topNode.contains(person));
	}

	@Test
	/**
	 * Here we want to test that Dad and Father are in the same node,
	 * because they have been defined as equivalent classes
	 */
	public void testDadFatherEquivalence() throws Exception {
		OWLOntology ont3 = ontManager.loadOntologyFromOntologyDocument(new File(localDirectoryForOntologies + "moreComplexParentWithequivalentClasses.owl"));
		OWLReasoner reasoner = new DMTReasonerFactory().createReasoner(ont3);

		HashSet<OWLClass> classes = new HashSet<>();

		OWLClass father = null;
		OWLClass dad = null;

		Set<OWLAxiom> axioms = ont3.getAxioms();
		for (OWLAxiom a : axioms) {
			classes.addAll(a.getClassesInSignature());
		}

		// Grab the father and grandfather classes
		for (OWLClass c : classes) {
			if (c.getIRI().toString().endsWith("Father")) {
				father = new OWLClassImpl(c.getIRI());
			}
			if (c.getIRI().toString().endsWith("Dad")) {
				dad = new OWLClassImpl(c.getIRI());
				System.out.println("DAD: " + dad);
			}
		}

		// If we didn't grab them, fail the test
		if (father == null || dad == null) {
			assertEquals("Father or dad is null", 0, 1);
		}

		Node<OWLClass> equivalentClasses = reasoner.getEquivalentClasses(father);

		// See that dad is the one and only equivalent class
		assertTrue(equivalentClasses.contains(dad));
		assertTrue(equivalentClasses.getSize() == 2);
	}
}
