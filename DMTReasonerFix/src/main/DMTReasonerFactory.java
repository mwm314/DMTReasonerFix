package main;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.reasoner.OWLReasonerConfiguration;
import org.semanticweb.owlapi.reasoner.OWLReasonerFactory;


public class DMTReasonerFactory implements OWLReasonerFactory {
	

	@Override
	public OWLReasoner createNonBufferingReasoner(OWLOntology ontology) {
		throw new DMTDoesNotSupportException("We only deal with buffering reasoners");
	}

	@Override
	public OWLReasoner createNonBufferingReasoner(OWLOntology ontology,
			OWLReasonerConfiguration config) {
		throw new DMTDoesNotSupportException("We only deal with buffering reasoners");
	}

	@Override
	public OWLReasoner createReasoner(OWLOntology ontology) {
		return new DMTReasoner(ontology, false, false);
	}
	
	/**
	 * Constructor to call if output to console desired or DAG visual desired
	 * @param ontology
	 * 			The ontology in question
	 * @param verbose
	 * 			Parameter to display text output to console
	 * @param showGraph
	 * 			Parameter to call and create a JFrame to display the DAG
	 * @return
	 */
	public OWLReasoner createReasoner(OWLOntology ontology, boolean verbose, boolean showGraph) {
		return new DMTReasoner(ontology, verbose, showGraph);
	}

	@Override
	public OWLReasoner createReasoner(OWLOntology ontology,
			OWLReasonerConfiguration config) {
		throw new DMTDoesNotSupportException("We do not handle configurations at this time");
	}

	@Override
	/**
	 * Returns the name of the reasoner
	 */
	public String getReasonerName() {
		return "Dan,Matt,Tyler ALHFN reasoner";
	}

}
