package aprove.prooftree.Obligations;

import java.io.*;
import java.util.*;
import java.util.function.Predicate;

import org.w3c.dom.*;

import aprove.api.prooftree.*;
import aprove.cli.*;
import aprove.input.Programs.llvm.processors.*;
import aprove.prooftree.*;
import aprove.prooftree.Export.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.CPF.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Logic.Implication.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;

/**
 * This class represents a node that encapsulates exactly one basic obligation.
 * @author thiemann, marmer
 */
public final class BasicObligationNode extends ObligationNode implements ChildAddProvider, CPF {

    /**
     * The data for CPF online checking
     */
    private static CPFOnlineChecker cpfOnlineChecker = null;

    public static void setCPFOnlineChecker(final CPFOnlineChecker checker) {
        BasicObligationNode.cpfOnlineChecker = checker;
    }

    /**
     * we have to determine which kind of proof we want to export
     * @param truthValue yes no maybe
     * @return true, if a termination proof is intended, false, if a nontermination proof is intended
     */
    private static boolean getPositive(final YNM truthValue) {
        switch (truthValue) {
        case YES:
            return true;
        case NO:
            return false;
        default:
            return true; // if there is a maybe, we create a partial positive proof
        }
    }

    /** Listeners waiting for new children of this node. */
    private final Collection<ChildAddListener> childListener;

    private Collection<OnlineCertificationListener> onlineCertificationListener;

    /** Children of this node (together with proofs leading to them). */
    private final List<ObligationNodeChild> children;

    /** Map for speedy access to proof and implications leading to some children */
    private final Map<ObligationNode, ObligationNodeChild> childrenMap;

    /** The encapsulated basic obligation. */
    private final BasicObligation theBObl;

    /**
     * Create a new node from a given basic obligation.
     * @param basicObligation some obligation
     */
    public BasicObligationNode(final BasicObligation basicObligation) {
        this.theBObl = basicObligation;
        this.childListener = new LinkedList<>();
        this.children = new LinkedList<>();
        this.childrenMap = new LinkedHashMap<>();
        this.onlineCertificationListener = new LinkedHashSet<>();

        this.addTruthValueListener(this);
    }

    /**
     * Create a new node from an encapsulated basic obligation.
     * @param basicObligationNode some obligation node
     */
    public BasicObligationNode(final BasicObligationNode basicObligationNode) {
        this(basicObligationNode.getBasicObligation());
    }

    /* (non-Javadoc)
     * @see aprove.xml.XMLProofExportable#adaptMetaData(aprove.xml.XMLMetaData)
     */
    @Override
    public XMLMetaData adaptMetaData(final XMLMetaData xmlMetaData) {
        return xmlMetaData;
    }

    /* (non-Javadoc)
     * @see aprove.prooftree.ChildAddProvider#addChildAddListener(aprove.prooftree.ChildAddListener)
     */
    @Override
    public synchronized Collection<ObligationNodeChild> addChildAddListener(
            final ChildAddListener listener) {
        this.childListener.add(listener);
        return this.getSuccessors();
    }

    /**
     * Note that some technique lead to a new obligation. Inform all relevant
     * listeners about this.
     *
     * @param newChild Some new obligation with a proof and obligation.
     */
    public synchronized void addTechnique(final ObligationNodeChild newChild, final boolean checkProof) {
        if (checkProof && BasicObligationNode.cpfOnlineChecker != null) {
            this.checkProofStep(newChild, BasicObligationNode.cpfOnlineChecker);
        }
        final ObligationNode childObl = newChild.getNewObligation();
        childObl.setDepth(this.getDepth() + 1);
        childObl.addTruthValueListener(this);

        this.children.add(newChild);
        this.childrenMap.put(newChild.getNewObligation(), newChild);

        if (this.updateTruth(newChild.getImplication(), childObl.getTruthValue())) {
            this.informTruthValueListeners(this.getTruthValue());
        }

        for (final ChildAddListener listener : this.childListener) {
            listener.childAdded(this, newChild);
        }
    }

    /* (non-Javadoc)
     * @see aprove.prooftree.Obligations.ObligationNode#checkProof(aprove.prooftree.Export.CPFOnlineChecker)
     */
    @Override
    public Triple<CPFCheckResult,String,String> checkProof(final String filename) {
        return CetaCPFChecker.checkCPF(this, filename);
    }

    /* (non-Javadoc)
     * @see aprove.prooftree.Export.Utility.Exportable#export(aprove.prooftree.Export.Utility.Export_Util)
     */
    @Override
    public String export(final Export_Util util) {
        final StringBuilder buf = new StringBuilder();

        buf.append(util.bold("Obligation type:"));
        buf.append(util.newline());
        buf.append(util.indent(this.getBasicObligation().getName(NameLength.LONG)
                + " (" + this.getBasicObligation().getName(NameLength.SHORT) + ")"));
        buf.append(util.newline());
        buf.append(util.hline());
        buf.append(util.newline());

        buf.append(util.bold("Truth value:"));
        buf.append(util.newline());
        buf.append(util.indent(this.getTruthValue().toString()));

        return buf.toString();
    }

    /**
     * @return basic obligation encapsulated by this obligation node.
     */
    public BasicObligation getBasicObligation() {
        return this.theBObl;
    }

    /* (non-Javadoc)
     * @see aprove.prooftree.Obligations.ObligationNode#getNonterminatingTerm()
     */
    @Override
    public TRSTerm getNonterminatingTerm() {
        /*
         * Prototypical implementation which requires the nontermination proof
         * to be the proof for the local BasicObligation itself.
         * TODO Also propagate info from proofs for child obligations.
         */
        final List<ObligationNodeChild> models = this.getProvingChildren();
        for (ObligationNodeChild model: models) {
            final Proof proof = model.getProof();
            if (proof instanceof HasNonterminatingTerm) {
                final HasNonterminatingTerm hasNTT = (HasNonterminatingTerm) proof;
                final TRSTerm nonTerminating = hasNTT.getNonterminatingTerm();
                return nonTerminating;
            }
        }
        return null;
    }

    public ObligationNodeChild getProvingChild() {
        // This is a hack which is needed for partial certification with lower bounds.
        // If we have a lower and an upper bound, then we have multiple proving children.
        // This is currently not supported and requires several changes. Since we are
        // running out of time w.r.t. a paper deadline, we use the following workaround for
        // the moment: Just drop the lower bound and take care that all lower bound proofs
        // are counted as unknown proofs via ObligationNode#noteUnknownLowerBoundsProofs.
        TruthValue truthValue = this.getTruthValue();
        if (truthValue instanceof ComplexityYNM) {
            ComplexityYNM complexity = (ComplexityYNM) truthValue;
            truthValue = ComplexityYNM.createUpper(complexity.getUpperBound());
        }
        return getProvingChild(truthValue::equals);
    }

    /**
     * @return some child node of <code>theModel</code> which constitutes a
     *         truth-value-establishing proof for <code>theNode</code> (if any;
     *         such nodes should only exist for BasicObligationNodes), null
     *         otherwise
     */
    public ObligationNodeChild getProvingChild(Predicate<TruthValue> eq) {
        if (this.isTruthValueKnown()) {
            for (final ObligationNodeChild child : this.children) {
                final ObligationNode newObl = child.getNewObligation();
                if (newObl.isTruthValueKnown()) {
                    try {
                        if (eq.test(child.getImplication()
                                .propagate(newObl.getTruthValue()))) {
                            return child;
                        }
                    } catch (IncompatibleTruthValueException e) {
                        continue;
                    }
                }
            }
        }
        return null;
    }

    public List<ObligationNodeChild> getProvingChildren() {
        TruthValue truthValue = this.getTruthValue();
        if (truthValue instanceof ComplexityYNM) {
            ComplexityYNM complexity = (ComplexityYNM) truthValue;
            ObligationNodeChild child = getProvingChild(complexity::equals);
            List<ObligationNodeChild> res = new ArrayList<>();
            if (child != null) {
                res.add(child);
            } else {
                Predicate<TruthValue> equalUpper = x -> x instanceof ComplexityYNM && ((ComplexityYNM) x).getUpperBound().equals(complexity.getUpperBound());
                Predicate<TruthValue> equalLower = x -> x instanceof ComplexityYNM && ((ComplexityYNM) x).getLowerBound().equals(complexity.getLowerBound());
                ObligationNodeChild upperChild = null;
                ObligationNodeChild lowerChild = null;
                if (complexity.getUpperBound().isFinite()) {
                    upperChild = getProvingChild(equalUpper);
                }
                if (!complexity.getLowerBound().isConstant()) {
                    lowerChild = getProvingChild(equalLower);
                }
                if (upperChild != null) {
                    res.add(upperChild);
                }
                if (lowerChild != null) {
                    res.add(lowerChild);
                }
            }
            return res;
        } else {
            ObligationNodeChild provingChild = getProvingChild();
            if (provingChild == null) {
                return Collections.emptyList();
            } else {
                return Collections.singletonList(provingChild);
            }
        }
    }

    /* (non-Javadoc)
     * @see aprove.prooftree.Obligations.ObligationNode#getRepresentation()
     */
    @Override
    public String getRepresentation() {
        return this.getBasicObligation().getName(NameLength.SHORT);
    }

    /* (non-Javadoc)
     * @see aprove.prooftree.Obligations.ObligationNode#getSuccessorCount()
     */
    @Override
    public int getSuccessorCount() {
        return this.children.size();
    }

    /**
     * @return list of successors of this obligation node, together with
     *  proofs and implications.
     */
    public List<ObligationNodeChild> getSuccessors() {
        return this.children;
    }

    /* (non-Javadoc)
     * @see aprove.prooftree.Obligations.ObligationNode#getTruthValue()
     */
    @Override
    public TruthValue getTruthValue() {
        return this.theBObl.getTruthValue();
    }

    /**
     * Merges all successors of another basic obligation node into this node.
     *
     * @param otherNode node of which we merge the successors into this node.
     */
    public synchronized void merge(final BasicObligationNode otherNode) {
        if (aprove.Globals.useAssertions) {
            assert (this.theBObl == otherNode.theBObl);
        }

        // Go through addTechnique to ensure that listeners are correctly
        // informed:
        for (final ObligationNodeChild newChild : otherNode.children) {
            this.addTechnique(newChild, true);
        }
    }

    /* (non-Javadoc)
     * @see aprove.prooftree.Obligations.ObligationNode#offersCertifiableTechniques()
     */
    @Override
    public boolean offersCertifiableTechniques() {
        return this.theBObl.offersCertifiableTechniques();
    }
    
    @Override
    public void printGraphmlWitness(String file) {
        List<ObligationNodeChild> children = this.getProvingChildren();
        for (ObligationNodeChild child : children) {
            if (child.getImplication().equals(YNMImplication.COMPLETE)
                    || child.getImplication().equals(YNMImplication.EQUIVALENT)) {
                if (child.getNewObligation().getTruthValue().equals(YNM.NO)) {
                    Proof proof = child.getProof();
                    if (proof instanceof HasGraphmlWitness) {
                        String witness = ((HasGraphmlWitness) proof).getGraphmlWitness();
                        if (witness != null) {
                            PrintWriter writer;
                            try {
                                writer = new PrintWriter(file, "UTF-8");
                                writer.print(witness);
                                writer.close();
                            } catch (Exception e) {
                                System.err.println(e.getMessage());
                            }
                            return;
                        }
                    }
                    child.getNewObligation().printGraphmlWitness(file);
                }
            }
        }
    }

    /* (non-Javadoc)
     * @see aprove.prooftree.Obligations.ObligationNode#recursiveRepropagateTruthValues()
     */
    @Override
    @Deprecated
    public void recursiveRepropagateTruthValues() {
        for (final ObligationNodeChild child : this.children) {
            final ObligationNode childNode = child.getNewObligation();
            childNode.recursiveRepropagateTruthValues();
            this.truthValueChanged(childNode.getTruthValue(), childNode);
        }
    }

    /* (non-Javadoc)
     * @see aprove.prooftree.ChildAddProvider#removeChildAddListener(aprove.prooftree.ChildAddListener)
     */
    @Override
    public void removeChildAddListener(final ChildAddListener listener) {
        this.childListener.remove(listener);
    }

    /* (non-Javadoc)
     * @see aprove.prooftree.Obligations.ObligationNode#setDepth(int)
     */
    @Override
    public void setDepth(final int depth) {
        super.setDepth(depth);
        final int deeperDepth = depth + 1;
        for (final ObligationNodeChild child : this.children) {
            child.getNewObligation().setDepth(deeperDepth);
        }
    }

    /* (non-Javadoc)
     * @see aprove.xml.CPFObligationNode#toCPF(org.w3c.dom.Document, boolean, aprove.xml.XMLMetaData, aprove.prooftree.Export.CPFExportStatistic)
     */
    @Override
    public Element toCPF(final Document doc, final boolean positive, final XMLMetaData xmlMetaData, final CPFExportStatistic statistics) {
        // this is a hack, see the javadoc comment of ObligationNode#noteUnknownLowerBoundsProofs for more information
        this.noteUnknownLowerBoundsProofs(statistics);
        final Triple<Proof, BasicObligationNode[], CPFModus> relevant = this.getRelevantChildren(positive);
        final Proof proof = relevant.x;
        final BasicObligationNode[] children = relevant.y;
        final CPFModus modus = relevant.z;
        if (proof == null) {
            statistics.addAssumption();
            return this.theBObl.getCPFAssumption(doc, xmlMetaData, modus, this.theBObl.getTruthValue());
        } else {
            final boolean checkable = proof.isCPFCheckableProof(modus);
            final XMLMetaData newMetaData = checkable ? proof.adaptMetaData(xmlMetaData) : null;
            final Element[] childrenProofs = new Element[children.length];
            for (int i = 0; i < children.length; i++) {
                childrenProofs[i] = children[i].toCPF(doc, positive, newMetaData, statistics);
            }
            if (!checkable) {
                statistics.addUnknown();
                String s = proof.getNonCPFExportableReason(modus);
                if (s == null) {
                    s = "unknown proof";
                }
                final Element desc = CPFTag.DESCRIPTION.create(doc, doc.createTextNode(s));
                final Element orig = this.theBObl.getCPFInput(doc, xmlMetaData, this.getTruthValue());
                final Element unsupported = CPFTag.UNKNOWN_PROOF.create(doc, desc, orig);
                for (int i = 0; i < children.length; i++) {
                    unsupported.appendChild(CPFTag.SUB_PROOF.create(doc,
                        children[i].theBObl.getCPFInput(doc, newMetaData, children[i].theBObl.getTruthValue()),
                            childrenProofs[i]));
                }
                if (modus.isPositive()) {
                    return proof.positiveTag().create(doc, unsupported);
                } else {
                    return proof.negativeTag().create(doc, unsupported);
                }
            } else {
                statistics.addReal();
                return proof.toCPF(doc, childrenProofs, xmlMetaData, modus);
            }
        }
    }

    @Override
    public void noteUnknownLowerBoundsProofs(CPFExportStatistic statistics) {
        if (this.getTruthValue() instanceof ComplexityYNM) {
            ComplexityYNM complexity = (ComplexityYNM) this.getTruthValue();
            if (!complexity.getLowerBound().isConstant()) {
                statistics.addUnknown();
            }
            for (ObligationNodeChild child: this.getSuccessors()) {
                child.getNewObligation().noteUnknownLowerBoundsProofs(statistics);
            }
        }
    }

    /**
     * writes the complete proof as CPF file. if the truthvalue is not determined,
     * then a partial positive proof is written.
     * @param out
     * @throws Exception
     */
    @Override
    public void writeCPF(final OutputStream out) throws Exception {
        ProofExport.exportCPF(this.theBObl,
                this.getTruthValue().fallbackToYNM() != YNM.fromBool(false),
                this,
            this.getTruthValue(),
                out);
    }

    /* (non-Javadoc)
     * @see aprove.xml.XMLProofExportable#toDOM(org.w3c.dom.Document, aprove.xml.XMLMetaData)
     */
    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {

        final Element e = XMLTag.OBL.createElement(doc);
        XMLAttribute.OBL_IDENTIFIER.setAttribute(e, this.theBObl.getId());
        XMLAttribute.COMMIT_ID.setAttribute(e, ExportManager.getCommitID());
        final Element f = XMLTag.PROPOSITION.createElement(doc);

        final Element bobl = XMLTag.BASIC_OBL.createElement(doc);
        bobl.appendChild(this.theBObl.toDOM(doc, xmlMetaData));
        f.appendChild(bobl);

        List<ObligationNodeChild> models = this.getProvingChildren();
        // If there is no proving child, use the first one:
        if (models.isEmpty()) {
            if (!this.children.isEmpty()) {
                models = Collections.singletonList(this.children.get(0));
            }
        }

        for (ObligationNodeChild model: models) {
            final Element proof = XMLTag.PROOF.createElement(doc);
            final Proof theProof = model.getProof();
            final XMLMetaData newMetaData = theProof.adaptMetaData(xmlMetaData);
            proof.appendChild(theProof.toDOM(doc, xmlMetaData));
            f.appendChild(proof);

            final Element impl = XMLTag.IMPLICATION.createElement(doc);
            XMLAttribute.IMPLICATION_VALUE.setAttribute(impl, model
                    .getImplication().toString().toLowerCase());
            f.appendChild(impl);

            f.appendChild(model.getNewObligation().toDOM(doc, newMetaData));
        }

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
    public synchronized void truthValueChanged(final TruthValue value,
            final ObligationNode source) {
        boolean change = false;

        if (this.childrenMap.containsKey(source)) {
            change |= this.updateTruth(this.childrenMap.get(source).getImplication(), value);
        }

        if (change) {
            this.informTruthValueListeners(this.getTruthValue());
        }
    }

    private void checkProofStep(final ObligationNodeChild newChild, final CPFOnlineChecker stats) {
        stats.incrementNrProofSteps();
        final Proof proof = newChild.getProof();
        final Implication impl = newChild.getImplication();
        final ObligationNode newObl = newChild.getNewObligation();
        if (!(impl instanceof YNMImplication)) {
            stats.incrementUnknownProofStructure();
            return;
        }
        final YNMImplication yimpl = (YNMImplication) impl;
        if (yimpl == YNMImplication.ANTIVALENT) {
            stats.incrementUnknownProofStructure();
            return;
        }
        final List<BasicObligationNode> children = new ArrayList<>();
        if (newObl instanceof BasicObligationNode) {
            children.add((BasicObligationNode) newObl);
        } else if (newObl instanceof JunctorObligationNode) {
            final JunctorObligationNode junctor = (JunctorObligationNode) newObl;
            for (final ObligationNode oblNode : junctor.getChildren()) {
                if (oblNode instanceof BasicObligationNode) {
                    children.add((BasicObligationNode) oblNode);
                } else {
                    stats.incrementUnknownProofStructure();
                    return;
                }
            }
        } else {
            stats.incrementUnknownProofStructure();
            return;
        }
        final boolean soundness = (yimpl == YNMImplication.SOUND || yimpl == YNMImplication.EQUIVALENT);
        final boolean completeness = (yimpl == YNMImplication.COMPLETE || yimpl == YNMImplication.EQUIVALENT);
        final List<CPFModus> modi = new ArrayList<>();
        final int n = children.size();
        if (soundness) {
            modi.add(CPFModusFactory.PROVE);
        }
        if (completeness) {
            for (int i = 0; i < n; i++) {
                modi.add(CPFModusFactory.disprove(i));
            }
        }
        modeloop: for (final CPFModus modus : modi) {
            final int nr = stats.incrementNrImplications();
            final String filename = stats.getFileName("" + nr);
            OutputStream ostream = null;
            if (!proof.isCPFCheckableProof(modus)) {
                stats.incrementUnsupportedAprove();
                try {
                    ostream = new BufferedOutputStream(new FileOutputStream(new File(filename + ".unsupported.txt")));
                    final OutputStreamWriter writer = new OutputStreamWriter(ostream);
                    writer.write(proof.getNonCPFExportableReason(modus) + " with " + modus + "\n");
                    writer.flush();
                    writer.close();
                } catch (final IOException e) {
                }
                continue modeloop;
            }
            final String cpfFileName = filename + ".partial.xml";
            final CPF cpf = new CPF() {

                @Override
                public void writeCPF(final OutputStream ostream) throws Exception {
                    final CPFObligationNode proofCPF = new CPFObligationNode() {

                        @Override
                        public Element toCPF(
                            final Document doc,
                            final boolean positive,
                            final XMLMetaData preMetaData,
                            final CPFExportStatistic statistic)
                        {
                            final XMLMetaData xmlMetaData = proof.adaptMetaData(preMetaData);
                            final List<Integer> idx = new ArrayList<>();
                            if (modus.isPositive()) {
                                final int n = children.size();
                                for (int i = 0; i < n; i++) {
                                    idx.add(i);
                                }
                            } else {
                                final int i = modus.negativeReason();
                                if (i != -1) {
                                    idx.add(i);
                                }
                            }
                            final Element[] childrenProofs = new Element[idx.size()];
                            int childCount = 0;
                            for (final int i : idx) {
                                Element prf;
                                if (proof.requireFullSubproof(modus, i)) {
                                    prf = children.get(i).toCPF(doc, modus.isPositive(), xmlMetaData, new CPFExportStatistic());
                                } else {
                                    final BasicObligation ithBObl = children.get(i).theBObl;
                                    prf = ithBObl.getCPFAssumption(doc, xmlMetaData, modus, ithBObl.getTruthValue());
                                }
                                childrenProofs[childCount] = prf;
                                childCount++;
                            }
                            return proof.toCPF(doc, childrenProofs, preMetaData, modus);
                        }

                    };
                    ProofExport.exportCPF(
                        BasicObligationNode.this.theBObl,
                        modus.isPositive(),
                        proofCPF,
                        BasicObligationNode.this.getTruthValue(),
                        ostream);
                    ostream.flush();
                    ostream.close();
                }

            };
            final Triple<CPFCheckResult,String,String> result = CetaCPFChecker.checkCPF(cpf,cpfFileName);
            switch (result.x) {
            case Certified:
                stats.incrementAccepted();
                new File(cpfFileName).deleteOnExit();
                break;
            case CeTAnotAvailable:
                new File(cpfFileName).deleteOnExit();
                // on purpose there is no break here
            case ErrorInvokingCertifier:
            case TimeoutByCertifier:
                stats.incrementProblemExecCertifier();
                break;
            case ErrorWhenGeneratingCPF:
                stats.incrementProblemExport();
                break;
            case RejectedByCertifier:
                stats.incrementRejected();
                break;
            case UnsupportedByCertifier:
                stats.incrementUnsupported();
                break;
            }
            this.informOnlineCertificationListener(result.x);
        }
    }

    /**
     * returns the list of relevant children for this node:
     * for a termination proof, all children are considered,
     * for a non-termination proof the first child with status NO is delivered
     * (and the mode will be returned with the index of this child),
     * and if this node has no children, a pair with first component null will be returned.
     */
    private Triple<Proof, BasicObligationNode[], CPFModus> getRelevantChildren(final boolean positive) {
        ObligationNodeChild model = null;
        final YNM desired = YNM.fromBool(positive);
        if (this.isTruthValueKnown() && this.getTruthValue().fallbackToYNM() == desired) {
            // if there is a proving child, then use it,
            model = this.getProvingChild();
        } else {
            // otherwise take any child that would allow to conclude the desired truth value
            for (final ObligationNodeChild child : this.children) {
                try {
                    if (child.getImplication().propagate(desired) == desired) {
                        model = child;
                        break;
                    }
                } catch (IncompatibleTruthValueException e) {
                    continue;
                }
            }
        }
        if (model != null) {
            final Proof theProof = model.getProof();
            final ObligationNode obligationNode = model.getNewObligation();
            BasicObligationNode[] childrenNodes;
            CPFModus modus = positive ? CPFModusFactory.PROVE : CPFModusFactory.disprove(0);
            if (obligationNode instanceof JunctorObligationNode) {
                if (!positive) {
                    modus = CPFModusFactory.disprove(-1);
                }
                final JunctorObligationNode junctor = (JunctorObligationNode) obligationNode;
                final List<ObligationNode> childrenList = junctor.getChildren();
                final int n = childrenList.size();
                final List<BasicObligationNode> children = new ArrayList<>(n);
                int i = 0;
                for (final ObligationNode oblNode : childrenList) {
                    if (oblNode instanceof BasicObligationNode &&
                            (positive || oblNode.getTruthValue() == YNM.NO)) {
                        final BasicObligationNode boblNode = (BasicObligationNode) oblNode;
                        if (positive) {
                            children.add(boblNode);
                        } else {
                            return new Triple<>(theProof, new BasicObligationNode[]{boblNode}, CPFModusFactory.disprove(i));
                        }
                    }
                    i++;
                }
                childrenNodes = new BasicObligationNode[children.size()];
                childrenNodes = children.toArray(childrenNodes);
            } else if (obligationNode instanceof BasicObligationNode) {
                childrenNodes = new BasicObligationNode[]{(BasicObligationNode) obligationNode};
            } else {
                throw new RuntimeException("Unknown proof structure in BasicObligationNode");
            }
            return new Triple<>(theProof, childrenNodes, modus);
        } else {
            return new Triple<>(null, null, positive ? CPFModusFactory.PROVE : CPFModusFactory.disprove(-1));
        }
    }

    /**
     * Updates the truth value.
     *
     * @param direction => , <= , <=>
     * @param childValue YNM
     * @return true iff the truth value changed by the update
     */
    private synchronized boolean updateTruth(final Implication direction,
            final TruthValue childValue) {
        final TruthValue oldValue = this.theBObl.getTruthValue();
        TruthValue newValue;
        try {
            newValue = oldValue.combine(direction.propagate(childValue));
        } catch (IncompatibleTruthValueException e) {
            throw new RuntimeException(e);
        }
        this.theBObl.setTruth(newValue);
        return !newValue.equals(oldValue);
    }

    public synchronized void addOnlineCertificationListener(OnlineCertificationListener listener) {
        this.onlineCertificationListener.add(listener);
    }

    protected synchronized void informOnlineCertificationListener(CPFCheckResult value) {
        for (OnlineCertificationListener listener : this.onlineCertificationListener) {
            listener.noteOnlineCertificationResult(value, this);
        }
    }
}
