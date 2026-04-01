package aprove.verification.dpframework.Orders.SAT;

import java.util.*;
import java.util.logging.*;

import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.Variable;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * An encoder for path orderings that is fully parameterizable via strategies.
 *
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public class ParameterizablePOEncoder extends AbstractPOEncoder {

    public static Logger log = Logger.getLogger("aprove.verification.dpframework.Orders.SAT.ParameterizablePOEncoder");

    /**
     * Create a new PO encoder.
     * @param formulaFactory A factory for propositional formulae.
     * @param quasi Whether to allow quasi-precedences.
     * @param multiset Whether to use multiset comparison.
     * @param lex Whether to use lexicographic comparison.
     * @param perm Whether to consider any permutation of arguments during
     * lexicographical comparison or only left-to-right order.
     * @param prec Whether to use a precedence.
     * @param xgengrc Whether to allow x >= c if c has minimal precedence.
     * @param restriction
     * @param afstype The kind of argument filtering to use.
     */
    public ParameterizablePOEncoder(
            final FormulaFactory<None> formulaFactory,
            final boolean quasi,
            final boolean multiset,
            final boolean lex,
            final boolean perm,
            final boolean prec,
            final boolean xgengrc,
            final int restriction,
            final AFSType afstype) {
        super(formulaFactory, quasi, multiset, lex, perm, prec, xgengrc,
                restriction, afstype);
    }

    /**
     * Determine what kind of path order is being used and create it.
     */
    @Override
    public AfsOrder getOrder(Set<Variable<None>> knownTrue, Afs afs) {

        Poset<FunctionSymbol> poset = null;
        Qoset<FunctionSymbol> qoset = null;
        if (this.quasi) {
            qoset = this.getQoset(knownTrue, afs);
        } else {
            poset = this.getPoset(knownTrue, afs);
        }
        StatusMap<FunctionSymbol> statusMap = null;
        if (this.perm || (this.multiset && this.lex)) {
            statusMap = this.getStatusMap(knownTrue, afs);
        }
        ExportableOrder<TRSTerm> order;
        if (this.multiset) {
            // RPO(S)
            if (this.quasi && this.lex) {
                order = QRPOS.create(qoset, statusMap);
            } else if (this.quasi) {
                order = QRPO.create(qoset);
            } else if (this.lex) {
                order = RPOS.create(poset, statusMap);
            } else {
                order = RPO.create(poset);
            }
        } else {
            // LPO(S)
            if (this.quasi && this.perm) {
                order = QLPOS.create(qoset, statusMap);
            } else if (this.quasi) {
                order = QLPO.create(qoset);
            } else if (this.perm) {
                order = LPOS.create(poset, statusMap);
            } else {
                order = LPO.create(poset);
            }
        }
        return new AfsOrder(afs, order);
    }

}
