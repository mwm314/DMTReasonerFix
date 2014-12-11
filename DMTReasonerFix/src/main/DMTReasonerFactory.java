package main;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.reasoner.OWLReasonerConfiguration;
import org.semanticweb.owlapi.reasoner.OWLReasonerFactory;


public class DMTReasonerFactory implements OWLReasonerFactory {

	@Override
	public OWLReasoner createNonBufferingReasoner(OWLOntology ontology) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public OWLReasoner createNonBufferingReasoner(OWLOntology ontology,
			OWLReasonerConfiguration config) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public OWLReasoner createReasoner(OWLOntology ontology) {
		return new DMTReasoner(ontology);
	}

	@Override
	public OWLReasoner createReasoner(OWLOntology ontology,
			OWLReasonerConfiguration config) {
		// TODO Auto-generated method stub
		return null;
	}

	/**
	 * Returns the name of the reasoner
	 */
	@Override
	public String getReasonerName() {
		return "Dan,Matt,Tyler ALHFN reasoner";
	}

}
