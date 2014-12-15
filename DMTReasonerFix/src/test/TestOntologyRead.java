package test;

import static org.junit.Assert.assertEquals;

import java.io.File;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import main.*;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.AxiomType;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataProperty;
import org.semanticweb.owlapi.model.OWLDatatype;
import org.semanticweb.owlapi.model.OWLLiteral;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLObjectIntersectionOf;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.reasoner.NodeSet;
import org.semanticweb.owlapi.reasoner.OWLReasoner;

import uk.ac.manchester.cs.owl.owlapi.OWLClassImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLDataFactoryImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLDataPropertyImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLDatatypeImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLLiteralImplString;
import uk.ac.manchester.cs.owl.owlapi.OWLNamedIndividualImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLObjectIntersectionOfImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLObjectPropertyImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLObjectSomeValuesFromImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLObjectUnionOfImpl;

//import com.github.jsonldjava.core.RDFDataset.IRI;
/**
 * Just an example of reading in an ontology
 *
 * @author Matt
 *
 */
public class TestOntologyRead {
	public static final IRI pizza_iri = IRI.create("http://www.co-ode.org/ontologies/pizza/pizza.owl");

	public static void main(String[] args) throws Exception {
		/*
		 * OWLOntologyManager inputOntologyManager =
		 * OWLManager.createOWLOntologyManager(); OWLOntologyManager
		 * outputOntologyManager = OWLManager.createOWLOntologyManager();
		 * 
		 * OWLOntology ont =
		 * inputOntologyManager.loadOntologyFromOntologyDocument(new
		 * File("path to ontology"));
		 */
		OWLOntologyManager ontManager = OWLManager.createOWLOntologyManager();
		//OWLOntology ont = ontManager.loadOntologyFromOntologyDocument(new File("C:\\Users\\Keechwa\\Documents\\GitHub\\DMTReasoner\\DTMreasoner\\src\\test\\testOntology.owl"));
		// OWLOntology ont2 = ontManager.loadOntologyFromOntologyDocument(new
		// File("C:\\Users\\Keechwa\\Documents\\GitHub\\DMTReasoner\\DTMreasoner\\src\\test\\simpleParent.owl"));
		OWLOntology ont3 = ontManager.loadOntologyFromOntologyDocument(new File("C:/Users/Matt/Desktop/FinalOntology/evenMoreComplexParent.owl"));
		Set<OWLAxiom> axioms = ont3.getAxioms();
		
		Iterator<OWLAxiom> iter = axioms.iterator();
		HashSet<OWLClass> classes = new HashSet<>();
		
		while (iter.hasNext()) {
			OWLAxiom axiom = iter.next();
			System.out.println("STRING: " + axiom.toString());
			System.out.println("Axiom class: " + axiom.getClass());
			System.out.println("TYPE: " + axiom.getAxiomType().toString());
			if (axiom.getAxiomType() == AxiomType.DISJOINT_CLASSES) {
				System.out.println("YES!");
			}
			System.out.println(axiom.getClassesInSignature());
			classes.addAll(axiom.getClassesInSignature());
		}
		OWLReasoner reasoner = new DMTReasonerFactory().createReasoner(ont3, true, true);
		HashSet<OWLClassExpression> union = new HashSet<>();
		union.add(classes.toArray(new OWLClass[0])[2]);
		union.add(classes.toArray(new OWLClass[0])[1]);
		System.out.println(reasoner.isSatisfiable(new OWLObjectIntersectionOfImpl(union)));
		System.out.println(union);
		// test();
		//test2();
		test3();
	}
	
	public static void test3() throws Exception {
		OWLOntologyManager ontManager = OWLManager.createOWLOntologyManager();
		// Load .owl file and reason over it
		OWLOntology ont3 = ontManager.loadOntologyFromOntologyDocument(new File("C:/Users/Matt/Desktop/FinalOntology/evenMoreComplexParent.owl"));
		OWLReasoner reasoner = new DMTReasonerFactory().createReasoner(ont3);

		HashSet<OWLClass> classes = new HashSet<>();

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
				mother = new OWLClassImpl(c.getIRI());
			}
		}

		// If we didn't grab parent, fail the test
		if (parent == null) {
			//assertEquals("Parent is null", 0, 1);
		}

		//Get all the superclasses of grandmother
		NodeSet<OWLClass> allSuperclasses = reasoner.getSuperClasses(grandmother, false);
		
		System.out.println("ALLSUPP: " + allSuperclasses);
	}

	public static void test2() throws Exception{
		OWLOntologyManager ontManager = OWLManager.createOWLOntologyManager();
		OWLOntology ont3 = ontManager.loadOntologyFromOntologyDocument(new File("C:/Users/Matt/Desktop/FinalOntology/evenMoreComplexParent.owl"));
		OWLReasoner reasoner = new DMTReasonerFactory().createReasoner(ont3);
		
		System.out.println("reasoning?");

		HashSet<OWLClass> classes = new HashSet<>();

		OWLClass parent = null;

		Set<OWLAxiom> axioms = ont3.getAxioms();
		for (OWLAxiom a : axioms) {
			classes.addAll(a.getClassesInSignature());
		}

		// Grab the father and grandfather classes
		for (OWLClass c : classes) {
			if (c.getIRI().toString().endsWith("Parent")) {
				parent = new OWLClassImpl(c.getIRI());
			}
		}
		
		System.out.println("TEST");

		// If we didn't grab them, fail the test
		if (parent == null) {
			System.out.println("null");
			assertEquals("Parent is null", 0, 1);
		}
		
		System.out.println("before");

		NodeSet<OWLClass> allSubclasses = reasoner.getSubClasses(parent, false);
		
		System.out.println("PRINTING:");
		System.out.println("ALL SUBCLASSES: " + allSubclasses);
	}

	public static void test() {
		OWLClass lecturer = new OWLClassImpl(IRI.create("lecturer"));
		OWLObjectProperty hasResearch = new OWLObjectPropertyImpl(IRI.create("hasResearch"));
		OWLObjectProperty isRelatedToResearch = new OWLObjectPropertyImpl(IRI.create("isRelatedToResearch"));
		OWLObjectProperty teaches = new OWLObjectPropertyImpl(IRI.create("teaches"));
		OWLNamedIndividual sWeb = new OWLNamedIndividualImpl(IRI.create("sWeb"));
		OWLClass course = new OWLClassImpl(IRI.create("course"));
		OWLClass researchArea = new OWLClassImpl(IRI.create("researchArea"));
		OWLDataProperty hasTitle = new OWLDataPropertyImpl(IRI.create("hasTitle"));
		OWLDatatype dt = new OWLDatatypeImpl(IRI.create("dt"));
		OWLLiteral asstprof = new OWLLiteralImplString("asstprof");
		
		OWLDataFactoryImpl df = new OWLDataFactoryImpl();
		
		OWLClassExpression relateToSomeResearchArea = df.getOWLObjectSomeValuesFrom(isRelatedToResearch, researchArea);
		OWLClassExpression hasResearchRelateToSomeResearchArea = df.getOWLObjectSomeValuesFrom(hasResearch, relateToSomeResearchArea);
		OWLClassExpression teachesAtLeastThreeCourse = df.getOWLObjectMinCardinality(3, teaches, course);
		OWLClassExpression hasTitleAsstProf = df.getOWLDataHasValue(hasTitle, asstprof);
		
		Set s1 = new HashSet();
		s1.add(lecturer);
		s1.add(hasResearchRelateToSomeResearchArea);
		s1.add(teachesAtLeastThreeCourse);
		s1.add(hasTitleAsstProf);
		
		OWLObjectIntersectionOf iof = df.getOWLObjectIntersectionOf(s1);
		
		System.out.println(iof.getNestedClassExpressions());
	}
}
