package test;

import static org.junit.Assert.*;

import java.io.File;
import java.util.HashSet;
import java.util.Set;

import main.DMTReasonerFactory;

import org.junit.Test;
import org.semanticweb.owlapi.apibinding.OWLManager;
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

/**
 * Class to test the DMTreasoner
 * 
 * @author Matt
 *
 */
public class TestDMTReasoner {
	OWLOntologyManager ontManager = OWLManager.createOWLOntologyManager();

	// Subsumption test
	// Test to show that father subsumes grandfather in the
	// evenMoreComplexParent.owl ontology
	@Test
	public void grandfatherSubClassOfFather() throws Exception {

		OWLOntology ont3 = ontManager.loadOntologyFromOntologyDocument(new File("C:/Users/Matt/Desktop/FinalOntology/evenMoreComplexParent.owl"));
		OWLReasoner reasoner = new DMTReasonerFactory().createReasoner(ont3);

		HashSet<OWLClassExpression> union = new HashSet<>();
		HashSet<OWLClass> classes = new HashSet<>();

		OWLClass father = null;
		OWLClass grandfather = null;

		Set<OWLAxiom> axioms = ont3.getAxioms();
		for (OWLAxiom a : axioms) {
			classes.addAll(a.getClassesInSignature());
		}

		for (OWLClass c : classes) {
			// System.out.println("IRI STRING: " + c.getIRI().toString());
			if (c.getIRI().toString().endsWith("Father")) {
				System.out.println("TRUE");
				father = new OWLClassImpl(c.getIRI());
			}
			if (c.getIRI().toString().endsWith("Grandfather")) {
				grandfather = new OWLClassImpl(c.getIRI());
			}
		}

		if (father == null || grandfather == null) {
			// Fail test
			assertEquals("Father is null", 0, 1);
		}

		NodeSet<OWLClass> directSubclasses = reasoner.getSubClasses(father, true);

		for (Node<OWLClass> n : directSubclasses) {
			System.out.println("Node entities: " + n.getEntities());
			if (n.contains(grandfather)) {
				assertEquals(0, 0);
				return;
			}
		}
		assertEquals(10, 11);

	}

	//Here we want to show the Parent subsumes Grandmother
	@Test
	public void grandmotherSubClassOfParent() throws Exception {

		OWLOntology ont3 = ontManager.loadOntologyFromOntologyDocument(new File("C:/Users/Matt/Desktop/FinalOntology/evenMoreComplexParent.owl"));
		OWLReasoner reasoner = new DMTReasonerFactory().createReasoner(ont3);

		HashSet<OWLClassExpression> union = new HashSet<>();
		HashSet<OWLClass> classes = new HashSet<>();

		OWLClass father = null;
		OWLClass grandfather = null;

		Set<OWLAxiom> axioms = ont3.getAxioms();
		for (OWLAxiom a : axioms) {
			classes.addAll(a.getClassesInSignature());
		}

		for (OWLClass c : classes) {
			// System.out.println("IRI STRING: " + c.getIRI().toString());
			if (c.getIRI().toString().endsWith("Father")) {
				System.out.println("TRUE");
				father = new OWLClassImpl(c.getIRI());
			}
			if (c.getIRI().toString().endsWith("Grandfather")) {
				grandfather = new OWLClassImpl(c.getIRI());
			}
		}

		if (father == null || grandfather == null) {
			// Fail test
			assertEquals("Father is null", 0, 1);
		}

		NodeSet<OWLClass> directSubclasses = reasoner.getSubClasses(father, true);

		for (Node<OWLClass> n : directSubclasses) {
			System.out.println("Node entities: " + n.getEntities());
			if (n.contains(grandfather)) {
				assertEquals(0, 0);
				return;
			}
		}
		assertEquals(10, 11);

	}

}
