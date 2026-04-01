package aprove.prooftree.Obligations;

import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Logic.*;
import aprove.xml.*;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

/**
 * A default basic obligation class.
 * The only missing methods are the export- and the init-truth-method
 *
 * @author thiemann
 */
public abstract class DefaultBasicObligation implements BasicObligation {

    /** Current truth value known for this obligation. */
    private TruthValue currentTruth;

    /** some unique string identifying this obligation. */
    private final String id;

    /**
     * A long name (i.e., "Q restricted TRS") for this obligation.
     */
    private final String longName;

    /**
     * The direct parent obligation
     */
    private BasicObligation parent;

    /**
     * A short name (i.e., "QTRS") for this obligation.
     */
    private final String shortName;

    /**
     * Creates a DefaultBasicObligation with a name description specifying that no name has been specified.
     */
    public DefaultBasicObligation() {
        this("Name of obligation not specified", "long name of obligation not specified");
    }

    /**
     * @param shortName
     * @param longName
     */
    public DefaultBasicObligation(final String shortName, final String longName) {
        this.id = ObligationNode.getNextObligationId();
        this.shortName = shortName;
        this.longName = longName;
        this.currentTruth = YNM.MAYBE;
    }

    /* (non-Javadoc)
     * @see aprove.prooftree.Obligations.BasicObligation#deepcopy()
     */
    @Override
    public BasicObligation deepcopy() {
        return null;
    }

    /* (non-Javadoc)
     * @see aprove.xml.CPFInputProblem#getCPFAssumption(org.w3c.dom.Document, aprove.xml.XMLMetaData, aprove.xml.CPFModus)
     */
    @Override
    public Element getCPFAssumption(
        final Document doc,
        final XMLMetaData xmlMetaData,
        final CPFModus modus,
        final TruthValue tv) {
        return CPFTag.UNKNOWN_INPUT_PROOF.create(doc,
            CPFTag.UNKNOWN_ASSUMPTION.create(
                doc, this.getCPFInput(doc, xmlMetaData, tv)));
    }

    /* (non-Javadoc)
     * @see aprove.xml.CPFInputProblem#getCPFInput(org.w3c.dom.Document, aprove.xml.XMLMetaData)
     */
    @Override
    public Element getCPFInput(final Document doc, final XMLMetaData xmlMetaData, final TruthValue tv) {
        return CPFTag.UNKNOWN_INPUT.create(
            doc,
            doc.createTextNode(this.getClass().getCanonicalName()));
    }

    /* (non-Javadoc)
     * @see aprove.prooftree.Obligations.BasicObligation#getId()
     */
    @Override
    public final String getId() {
        return this.id;
    }

    /* (non-Javadoc)
     * @see aprove.prooftree.Obligations.BasicObligation#getName(aprove.verification.dpframework.NameLength)
     */
    @Override
    public String getName(final NameLength length) {
        switch (length) {
        case SHORT:
            return this.shortName;
        case LONG:
            return this.longName;
        default:
            return "Unknown length for a name: " + length;
        }
    }

    /* (non-Javadoc)
     * @see aprove.prooftree.Obligations.BasicObligation#getObligationType()
     */
    @Override
    public ObligationType getObligationType() {
        return ObligationType.UNKNOWN;
    }

    /** {non-Javadoc}
     * @see aprove.prooftree.Obligations.BasicObligation#getParent()
     */
    @Override
    public BasicObligation getParent() {
        return this.parent;
    }

    /* (non-Javadoc)
     * @see aprove.prooftree.Obligations.BasicObligation#getTruthValue()
     */
    @Override
    public TruthValue getTruthValue() {
        return this.currentTruth;
    }

    /* (non-Javadoc)
     * @see aprove.prooftree.Obligations.BasicObligation#maybeCopy()
     */
    @Override
    public BasicObligation maybeCopy() {
        return this;
    }

    /**
     * is there CPF-export for this kind of obligation.
     * Should be overwritten, whenever getCPFInput/getCPFAssumption are overwritten
     */
    @Override
    public boolean offersCertifiableTechniques() {
        return false;
    }

    /**
     * Set direct parent obligation
     */
    public void setParent(BasicObligation parent) {
        this.parent = parent;
    }

    /* (non-Javadoc)
     * @see aprove.prooftree.Obligations.BasicObligation#setTruth(aprove.verification.oldframework.Logic.TruthValue)
     */
    @Override
    public void setTruth(final TruthValue t) {
        this.currentTruth = t;
    }

    /* (non-Javadoc)
     * @see aprove.xml.XMLObligationExportable#toDOM(org.w3c.dom.Document, aprove.xml.XMLMetaData)
     */
    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        final Element e = XMLTag.UNKNOWN_OBLIGATION.createElement(doc);
        e.appendChild(doc.createTextNode(this.getClass().getCanonicalName() + " is not formalized yet!"));
        return e;
    }

}
