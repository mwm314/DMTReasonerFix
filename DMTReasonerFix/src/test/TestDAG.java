package test;
import static org.junit.Assert.*;
import main.DMTReasoner;

import org.jgraph.graph.DefaultEdge;
import org.jgrapht.experimental.dag.DirectedAcyclicGraph;
import org.junit.Test;
import org.semanticweb.owlapi.reasoner.Node;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.reasoner.impl.*;
import org.semanticweb.owlapi.model.*;

import uk.ac.manchester.cs.owl.owlapi.*;

/**
 * Unit tests for testing the DAG structure
 * 
 * @author Matt
 *
 */
public class TestDAG {

	/**
	 *          TOP
	 *     MIDDLE  MIDDLE2
	 *     	   BOTTOM
	 */
	@Test
	public void testGetBottomClassNode() throws Exception{
		
		IRI owlNothing = IRI.create("owl:Nothing");
		OWLClassImpl bottomClass = new OWLClassImpl(owlNothing);
		
		DirectedAcyclicGraph<Node<OWLClass>, DefaultEdge> classNodeHierarchy = setClassDag();
		
		
		DMTReasoner test = new DMTReasoner();
		test.setClassNodeHierarchy(classNodeHierarchy);
		
		System.out.println("TEST- Loaded up DAG");
		test.getBottomClassNode();
		System.out.println("TEST- getBottomClassNode SUCESS");
		assertEquals(true, test.getBottomClassNode().contains(bottomClass));
		
		test.getBottomDataPropertyNode();
		System.out.println("TEST- DONE");
		
	}
	
	@Test
	public void testGetBottomDataPropertyNode() throws Exception{

		DirectedAcyclicGraph<Node<OWLDataProperty>, DefaultEdge> dataPropertyNodeHierarchy = setDataPropertyDag();
		
		IRI owlNothing = IRI.create("owl:Nothing");
		OWLDataPropertyImpl bottomDataProperty = new OWLDataPropertyImpl(owlNothing);
		
		DMTReasoner test = new DMTReasoner();
		test.setDataPropertyNodeHierarchy(dataPropertyNodeHierarchy);
		
		System.out.println("TEST- Loaded up DAG");
		test.getBottomClassNode();
		System.out.println("TEST- getBottomDataPropertyNode SUCESS");
		assertEquals(true, test.getBottomDataPropertyNode().contains(bottomDataProperty));
		
		test.getBottomDataPropertyNode();
		System.out.println("TEST- DONE");
		
	}
	
	@Test
	public void testGetBottomObjectPropertyNode() throws Exception{

		DirectedAcyclicGraph<Node<OWLObjectPropertyExpression>, DefaultEdge> objectPropertyNodeHierarchy = setObjectPropertyDag();
		
		IRI owlNothing = IRI.create("owl:Nothing");
		OWLObjectPropertyImpl bottomObjectProperty = new OWLObjectPropertyImpl(owlNothing);

		
		DMTReasoner test = new DMTReasoner();
		test.setObjectPropertyNodeHierarchy(objectPropertyNodeHierarchy);
		
		System.out.println("TEST- Loaded up DAG");
		test.getBottomClassNode();
		System.out.println("TEST- getBottomObjectPropertyNode SUCESS");
		assertEquals(true, test.getBottomObjectPropertyNode().contains(bottomObjectProperty));
		
		test.getBottomObjectPropertyNode();
		System.out.println("TEST- DONE");
	}
	private DirectedAcyclicGraph<Node<OWLClass>, DefaultEdge> setClassDag() throws Exception{
		
		DirectedAcyclicGraph<Node<OWLClass>, DefaultEdge> dag = new DirectedAcyclicGraph<Node<OWLClass>, DefaultEdge>(DefaultEdge.class);
		OWLClassNode classBottomNode = new OWLClassNode();
		OWLClassNode classMiddleNode1 = new OWLClassNode();
		OWLClassNode classMiddleNode2 = new OWLClassNode();
		OWLClassNode classTopNode = new OWLClassNode();
		IRI owlNothing = IRI.create("owl:Nothing");
		IRI owlclassMiddle1 = IRI.create("owl:classMiddle1");
		IRI owlclassMiddle2 = IRI.create("owl:classMiddle2");
		IRI owlThing = IRI.create("owl:Thing");
		
		OWLClassImpl bottomClass = new OWLClassImpl(owlNothing);
		OWLClassImpl middleClass = new OWLClassImpl(owlclassMiddle1);
		OWLClassImpl middle2Class = new OWLClassImpl(owlclassMiddle2);
		OWLClassImpl topClass = new OWLClassImpl(owlThing);
		
		classBottomNode.add(bottomClass);
		classMiddleNode1.add(middleClass);
		classTopNode.add(topClass);
		classMiddleNode2.add(middle2Class);
		
		dag.addVertex(classBottomNode);
		dag.addVertex(classMiddleNode1);
		dag.addVertex(classMiddleNode2);
		dag.addVertex(classTopNode);
		
		dag.addDagEdge(classBottomNode, classMiddleNode1);
		dag.addDagEdge(classBottomNode, classMiddleNode2);
		dag.addDagEdge(classMiddleNode1, classTopNode);
		dag.addDagEdge(classMiddleNode2, classTopNode);
		return dag;
	
	}
	
	private DirectedAcyclicGraph<Node<OWLDataProperty>, DefaultEdge> setDataPropertyDag() throws Exception{
		
		DirectedAcyclicGraph<Node<OWLDataProperty>, DefaultEdge> dag = new DirectedAcyclicGraph<Node<OWLDataProperty>, DefaultEdge>(DefaultEdge.class);
		OWLDataPropertyNode dataPropertyBottomNode = new OWLDataPropertyNode();
		OWLDataPropertyNode dataPropertyMiddleNode1 = new OWLDataPropertyNode();
		OWLDataPropertyNode dataPropertyMiddleNode2 = new OWLDataPropertyNode();
		OWLDataPropertyNode dataPropertyTopNode = new OWLDataPropertyNode();
		IRI owlNothing = IRI.create("owl:Nothing");
		IRI owlDataPropertyMiddle1 = IRI.create("owl:classMiddle1");
		IRI owlDataPropertyMiddle2 = IRI.create("owl:classMiddle2");
		IRI owlThing = IRI.create("owl:Thing");
		
		OWLDataPropertyImpl bottomDataProperty = new OWLDataPropertyImpl(owlNothing);
		OWLDataPropertyImpl middle1DataProperty = new OWLDataPropertyImpl(owlDataPropertyMiddle1);
		OWLDataPropertyImpl middle2DataProperty = new OWLDataPropertyImpl(owlDataPropertyMiddle2);
		OWLDataPropertyImpl topClass = new OWLDataPropertyImpl(owlThing);
		
		dataPropertyBottomNode.add(bottomDataProperty);
		dataPropertyMiddleNode1.add(middle1DataProperty);
		dataPropertyTopNode.add(topClass);
		dataPropertyMiddleNode2.add(middle2DataProperty);
		
		dag.addVertex(dataPropertyBottomNode);
		dag.addVertex(dataPropertyMiddleNode1);
		dag.addVertex(dataPropertyMiddleNode2);
		dag.addVertex(dataPropertyTopNode);
		
		dag.addDagEdge(dataPropertyBottomNode, dataPropertyMiddleNode1);
		dag.addDagEdge(dataPropertyBottomNode, dataPropertyMiddleNode2);
		dag.addDagEdge(dataPropertyMiddleNode1, dataPropertyTopNode);
		dag.addDagEdge(dataPropertyMiddleNode2, dataPropertyTopNode);
		return dag;
	
	}
	
	private DirectedAcyclicGraph<Node<OWLObjectPropertyExpression>, DefaultEdge> setObjectPropertyDag() throws Exception{
		
		DirectedAcyclicGraph<Node<OWLObjectPropertyExpression>, DefaultEdge> dag = new DirectedAcyclicGraph<Node<OWLObjectPropertyExpression>, DefaultEdge>(DefaultEdge.class);
		OWLObjectPropertyNode objectPropertyBottomNode = new OWLObjectPropertyNode();
		OWLObjectPropertyNode objectPropertyMiddleNode1 = new OWLObjectPropertyNode();
		OWLObjectPropertyNode objectPropertyMiddleNode2 = new OWLObjectPropertyNode();
		OWLObjectPropertyNode objectPropertyTopNode = new OWLObjectPropertyNode();
		IRI owlNothing = IRI.create("owl:Nothing");
		IRI owlObjectPropertyMiddle1 = IRI.create("owl:classMiddle1");
		IRI owlObjectPropertyMiddle2 = IRI.create("owl:classMiddle2");
		IRI owlThing = IRI.create("owl:Thing");
		
		OWLObjectPropertyImpl bottomObjectProperty = new OWLObjectPropertyImpl(owlNothing);
		OWLObjectPropertyImpl middle1ObjectProperty = new OWLObjectPropertyImpl(owlObjectPropertyMiddle1);
		OWLObjectPropertyImpl middle2ObjectProperty = new OWLObjectPropertyImpl(owlObjectPropertyMiddle2);
		OWLObjectPropertyImpl topClass = new OWLObjectPropertyImpl(owlThing);
		
		objectPropertyBottomNode.add(bottomObjectProperty);
		objectPropertyMiddleNode1.add(middle1ObjectProperty);
		objectPropertyTopNode.add(topClass);
		objectPropertyMiddleNode2.add(middle2ObjectProperty);
		
		dag.addVertex(objectPropertyBottomNode);
		dag.addVertex(objectPropertyMiddleNode1);
		dag.addVertex(objectPropertyMiddleNode2);
		dag.addVertex(objectPropertyTopNode);
		
		dag.addDagEdge(objectPropertyBottomNode, objectPropertyMiddleNode1);
		dag.addDagEdge(objectPropertyBottomNode, objectPropertyMiddleNode2);
		dag.addDagEdge(objectPropertyMiddleNode1, objectPropertyTopNode);
		dag.addDagEdge(objectPropertyMiddleNode2, objectPropertyTopNode);
		return dag;
	
	}
}