package test;

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
		OWLOntology ont = ontManager.loadOntologyFromOntologyDocument(new File("C:\\Users\\Keechwa\\Documents\\GitHub\\DMTReasoner\\DTMreasoner\\src\\test\\testOntology.owl"));
		// OWLOntology ont2 = ontManager.loadOntologyFromOntologyDocument(new
		// File("C:\\Users\\Keechwa\\Documents\\GitHub\\DMTReasoner\\DTMreasoner\\src\\test\\simpleParent.owl"));
		OWLOntology ont3 = ontManager.loadOntologyFromOntologyDocument(new File("C:\\Users\\Keechwa\\Documents\\GitHub\\DMTReasonerFix\\DMTreasonerFix\\src\\test\\moreComplexParentWithEquivalentClasses.owl"));
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
		OWLReasoner reasoner = new DMTReasonerFactory().createReasoner(ont3);
		HashSet<OWLClassExpression> union = new HashSet<>();
		union.add(classes.toArray(new OWLClass[0])[0]);
		union.add(classes.toArray(new OWLClass[0])[1].getComplementNNF());
		System.out.println(reasoner.isSatisfiable(new OWLObjectUnionOfImpl(union)));
		System.out.println(union);
		// test();
		// test2();
	}

	public static void test2() {
		OWLClassExpression male = new OWLClassImpl(IRI.create("Male"));
		OWLObjectPropertyExpression hasChild = new OWLObjectPropertyImpl(IRI.create("hasChild"));
		OWLObjectSomeValuesFrom test = new OWLObjectSomeValuesFromImpl(hasChild, male);
		OWLClassExpression maleNeg = male.getComplementNNF();
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
