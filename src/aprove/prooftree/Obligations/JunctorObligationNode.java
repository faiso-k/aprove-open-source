package aprove.prooftree.Obligations;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.api.prooftree.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.Junctors.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.CPF.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;

/**
 * A junctor obligation node is a junction (or/and/cond) of a list of obligation nodes.
 * @author thiemann
 */
public final class JunctorObligationNode extends ObligationNode {

    /**
     * @param junctor some junctor.
     * @param obls collection of obligations.
     * @return new <code>junctor</code> obligation connecting <code>obls</code>.
     */
    public static ObligationNode create(final IJunctor junctor, final Collection<? extends ObligationNode> obls) {
        final int n = obls.size();
        if (n == 1) {
            return obls.iterator().next();
        }
        final ObligationNode[] theObls = new ObligationNode[n];
        int i = 0;
        for (final ObligationNode obl : obls) {
            theObls[i] = obl;
            i++;
        }
        if (Globals.useAssertions) {
            assert(i == n);
        }
        return new JunctorObligationNode(junctor, theObls);
    }

    /**
     * @param obls collection of obligations.
     * @return new AND obligation connecting <code>obls</code>.
     */
    public static ObligationNode createAnd(final Collection<? extends ObligationNode> obls) {
        return JunctorObligationNode.create(Junctors.AND, obls);
    }

    /**
     * @param cond some obligation.
     * @param obl some other obligations
     * @return new COND obligation of <code>cond</code> and <code>obl</code>,
     *  where <code>obl</code>'s truth value is propagated only iff <code>cond
     *  </code> is TRUE.
     */
    public static ObligationNode createCond(final ObligationNode cond, final ObligationNode obl) {
        final ArrayList<ObligationNode> obls = new ArrayList<ObligationNode>(2);
        obls.add(cond);
        obls.add(obl);
        return JunctorObligationNode.create(Junctors.COND, obls);
    }

    /**
     * @param obls collection of obligations.
     * @return new OR obligation connecting <code>obls</code>.
     */
    public static ObligationNode createOr(final Collection<? extends ObligationNode> obls) {
        return JunctorObligationNode.create(Junctors.OR, obls);
    }

    /**
     * The truth value obtained by combining the children truth values according
     * to the supplied junctor.
     */
    private TruthValue currentTruthValue;

    /**
     * Some unique ID for this obligation.
     */
    private final String id;

    /**
     * The actual junctor of this node.
     */
    private final IJunctor junctor;

    /**
     * The child obligations connected by the junctor.
     */
    private final ObligationNode[] theObls;

    /**
     * Creates a JunctorObligationNode from an IJunctor and an array of ObligationNodes.
     * @param junctor The junctor.
     * @param obls The obligations.
     */
    private JunctorObligationNode(final IJunctor junctor, final ObligationNode[] obls) {
        this.id = ObligationNode.getNextObligationId();
        this.junctor = junctor;

        this.theObls = obls;
        // add the listeners
        for (final ObligationNode theObl : this.theObls) {
            theObl.addTruthValueListener(this);
        }
        this.currentTruthValue = YNM.MAYBE;
        this.calculateAndUpdateTruthValue();

        this.setDepth(this.getDepth());
    }

    /* (non-Javadoc)
     * @see aprove.xml.XMLProofExportable#adaptMetaData(aprove.xml.XMLMetaData)
     */
    @Override
    public XMLMetaData adaptMetaData(XMLMetaData metaData) {
        return metaData;
    }

    /* (non-Javadoc)
     * @see aprove.prooftree.Obligations.ObligationNode#checkProof(aprove.prooftree.Export.CPFOnlineChecker)
     */
    @Override
    public Triple<CPFCheckResult, String, String> checkProof(String filename) {
        return new Triple<>(CPFCheckResult.NoBasicObligation, null, null);
    }

    /* (non-Javadoc)
     * @see aprove.prooftree.Export.Utility.Exportable#export(aprove.prooftree.Export.Utility.Export_Util)
     */
    @Override
    public String export(final Export_Util util) {
        return util.export(this.getRepresentation());
    }

    /**
     * @return the child obligations of this node.
     */
    public synchronized List<ObligationNode> getChildren() {
        final List<ObligationNode> childs = new Vector<ObligationNode>(this.theObls.length);
        for (final ObligationNode model : this.theObls) {
            childs.add(model);
        }
        return childs;
    }

    /* (non-Javadoc)
     * @see aprove.prooftree.Obligations.ObligationNode#getNonterminatingTerm()
     */
    @Override
    public TRSTerm getNonterminatingTerm() {
        throw new aprove.verification.oldframework.Exceptions.NotYetHandledException(
            "Propagating non-terminating start terms over JunctorNodes has not yet been implemented."
        );
    }

    /* (non-Javadoc)
     * @see aprove.prooftree.Obligations.ObligationNode#getRepresentation()
     */
    @Override
    public String getRepresentation() {
        return this.junctor.getName(this.theObls.length);
    }

    /* (non-Javadoc)
     * @see aprove.prooftree.Obligations.ObligationNode#getSuccessorCount()
     */
    @Override
    public synchronized int getSuccessorCount() {
        return this.theObls.length;
    }

    /* (non-Javadoc)
     * @see aprove.prooftree.Obligations.ObligationNode#getTruthValue()
     */
    @Override
    public TruthValue getTruthValue() {
        return this.currentTruthValue;
    }

    /* (non-Javadoc)
     * @see aprove.prooftree.Obligations.ObligationNode#offersCertifiableTechniques()
     */
    @Override
    public boolean offersCertifiableTechniques() {
        return true;
    }
    
    @Override
    public void printGraphmlWitness(String file) {
        List<ObligationNode> nodes = this.getChildren();
        for (ObligationNode node : nodes) {
            if (node.getTruthValue().equals(YNM.NO)) {
                node.printGraphmlWitness(file);
            }
        }
    }

    /* (non-Javadoc)
     * @see aprove.prooftree.Obligations.ObligationNode#recursiveRepropagateTruthValues()
     */
    @Override
    @Deprecated
    public void recursiveRepropagateTruthValues() {

        //In the case we are a leaf, inform our parents about our truth value
        if (this.getSuccessorCount() == 0) {
            if (this.calculateAndUpdateTruthValue()) {
                this.informTruthValueListeners(this.currentTruthValue);
            }
        }

        //Otherwise, ask our children to search for a leaf:
        for (final ObligationNode child : this.getChildren()) {
            child.recursiveRepropagateTruthValues();
        }
    }

    /* (non-Javadoc)
     * @see aprove.prooftree.Obligations.ObligationNode#setDepth(int)
     */
    @Override
    public void setDepth(final int depth) {
        super.setDepth(depth);
        final int deeperDepth = depth + 1;
        for (final ObligationNode child : this.theObls) {
            child.setDepth(deeperDepth);
        }
    }

    /* (non-Javadoc)
     * @see aprove.xml.CPFObligationNode#toCPF(org.w3c.dom.Document, boolean, aprove.xml.XMLMetaData, aprove.prooftree.Export.CPFExportStatistic)
     */
    @Override
    public Element toCPF(
        final Document doc,
        final boolean modus,
        final XMLMetaData metaData,
        final CPFExportStatistic statistic)
    {
        throw new RuntimeException("Cannot print CPF for JunctionObligationNodes");
    }

    /* (non-Javadoc)
     * @see aprove.xml.XMLProofExportable#toDOM(org.w3c.dom.Document, aprove.xml.XMLMetaData)
     */
    @Override
    public Element toDOM(final Document doc, final XMLMetaData metaData) {
        XMLTag tag;
        if (this.junctor == Junctors.AND) {
            tag = XMLTag.CONJUNCTION;
        } else if (this.junctor == Junctors.OR) {
            tag = XMLTag.DISJUNCTION;
        } else if (this.junctor == Junctors.YES) {
            tag = XMLTag.PROVED;
        } else if (this.junctor == Junctors.NO) {
            tag = XMLTag.DISPROVED;
        } else {
            final Element e = doc.createElement("ERROR");
            e.appendChild(doc.createComment("unknown junctionObligation: "+this.junctor));
            return e;
        }

        final Element e = XMLTag.OBL.createElement(doc);
        XMLAttribute.OBL_IDENTIFIER.setAttribute(e, this.id);

        final Element f = tag.createElement(doc);
        CollectionUtils.addChildren(this.theObls, f, doc, metaData);
        e.appendChild(f);

        return e;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    /* (non-Javadoc)
     * @see aprove.prooftree.TruthValueListener#truthValueChanged(aprove.verification.oldframework.Logic.TruthValue, aprove.prooftree.Obligations.ObligationNode)
     */
    @Override
    public synchronized void truthValueChanged(final TruthValue value, final ObligationNode source) {
        if (this.calculateAndUpdateTruthValue()) {
            this.informTruthValueListeners(this.currentTruthValue);
        }
    }

    /**
     * updates the truth value from the children list
     * @return true iff the value has changed
     */
    private synchronized boolean calculateAndUpdateTruthValue() {
        final TruthValue oldTruth = this.currentTruthValue;
        final List<TruthValue> truthValues = new LinkedList<TruthValue>();
        for (final ObligationNode child : this.theObls) {
            truthValues.add(child.getTruthValue());
        }
        final TruthValue truth = this.junctor.combine(truthValues);
        this.currentTruthValue = truth;
        return !truth.equals(oldTruth);
    }

    @Override
    public void noteUnknownLowerBoundsProofs(CPFExportStatistic statistics) {
        for (ObligationNode child: this.getChildren()) {
            child.noteUnknownLowerBoundsProofs(statistics);
        }
    }
}
