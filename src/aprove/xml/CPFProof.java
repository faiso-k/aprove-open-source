package aprove.xml;

import org.w3c.dom.*;

public interface CPFProof {

    /**
     * export a proof to CPF format,
     * one can assume that the relevant proofs of subproofs are given in
     * chilrenProofs (i.e., all subproofs for termination proofs and
     * usually one subproof for non-termination proofs). The modus indicates
     * which kind of proof should be generated (a proof (positive), or a disproof).
     * Moreover, in the latter case, usually there is a number indicating the
     * index of the subproblem. So, e.g., if there is a non-termination proof for
     * the dependency-graph, then childrenProofs has length 1, and the number in the
     * modus indicates the i-th real SCC (where i starts counting from 0).
     * @param doc
     * @param childrenProofs
     * @param xmlMetaData
     * @param modus
     * @return
     */
    Element toCPF(Document doc, Element[] childrenProofs, XMLMetaData xmlMetaData, CPFModus modus);

    XMLMetaData adaptMetaData(XMLMetaData xmlMetaData);

    /**
     * will there be some checkable proof exported, when invoking toCPF with the given modus
     */
    boolean isCPFCheckableProof(CPFModus modus);

    /**
     * give some explanation why this proof cannot be exported
     */
    String getNonCPFExportableReason(CPFModus modus);

    /**
     * delivers the tag that should be used for proofs
     */
    CPFTag positiveTag();

    /**
     * delivers the tag that should be used for disproofs
     */
    CPFTag negativeTag();

    /**
     * check whether for the i-th subproof, it is is not allowed
     * to just use an assumption here for online certification.
     * E.g., for the Split-Processor, the first subproof must
     * fully be checked, as it cannot be checked stand-alone, as this
     * would require relative DP-problems which are not supported by
     * AProVE. In principal, if a sub-strategy is spawned where
     * online certification is disabled, then for this sub-proof
     * requireFullSubproof should return true. In all other cases,
     * the method should return false.
     */
    boolean requireFullSubproof(CPFModus modus, int i);

}
