package aprove.verification.oldframework.IntTRS.Ranking;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.solver.Engines.*;
import aprove.solver.Engines.SMTEngine.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.SMTLIBRatComparison.*;

/**
 * This class represents a so-called transition invariant, which is
 * a union of finitely many well-founded relations.
 * @author Matthias Hoelzel
 */
public class TransitionInvariant implements Exportable {
    /** Stores the relations this transition invariant contains */
    private final List<TransitionRelation> relations;

    /** Constructor! Create a empty transition invariant. */
    public TransitionInvariant() {
        this.relations = new LinkedList<>();
    }

    /**
     * Checks whether or not a given transition relation is included in this.
     * @param tr check whether or not the other relation is included
     * @param aborter some aborter
     * @return true if tr is certainly included
     * @throws AbortionException can be aborted
     */
    public boolean isCertainlySupersetOf(final TransitionRelation tr, final Abortion aborter) throws AbortionException {
        if (tr == null) {
            assert false : "Invalid relation!";
            return false;
        }
        final FormulaFactory<SMTLIBTheoryAtom> factory = new FullSharingFactory<>();
        final List<Formula<SMTLIBTheoryAtom>> formulas = new LinkedList<>();
        for (final SMTLIBRatGE libratge : tr.getPCS().toSMT(true)) {
            formulas.add(factory.buildTheoryAtom(libratge));
        }

        for (final TransitionRelation r : this.relations) {
            if (!(r instanceof Ranking) || !r.getStartSymbol().equals(tr.getStartSymbol())
                    || !r.getEndSymbol().equals(tr.getEndSymbol())) {
                continue;
            }

            final TransitionRelation renamed = r.renameStartAndEndVariables(tr, aborter);
            final List<SMTLIBRatGE> libratges = renamed.getPCS().toSMT(true);
            final List<Formula<SMTLIBTheoryAtom>> clause = new LinkedList<>();
            for (final SMTLIBRatGE libratge : libratges) {
                clause.add(factory.buildTheoryAtom(libratge));
            }
            final Formula<SMTLIBTheoryAtom> formula = factory.buildNot(factory.buildAnd(clause));
            formulas.add(formula);
        }

        final SMTEngine smtEngine = new YicesEngine();

        try {
            final YNM ynm = smtEngine.satisfiable(formulas, SMTLogic.QF_LRA, aborter);

            return ynm.equals(YNM.NO);
        } catch (final WrongLogicException e) {
            return false;
        }
    }

    /**
     * Adds a given relation.
     * @param tr to be added
     */
    public void addRelation(final TransitionRelation tr) {
        if (tr == null || !tr.isCertainlyWellFounded()) {
            assert false : "Cannot add invalid relation!";
            return;
        }
        this.relations.add(tr);
    }

    /**
     * Removes a given relation.
     */
    public void removeRelation(final TransitionRelation tr) {
        if (Globals.DEBUG_MATTHIAS) {
            assert this.relations.contains(tr) : "";
        }
        this.relations.remove(tr);
    }

    /**
     * Getter for the relations.
     * @return list of transition relations
     */
    public List<TransitionRelation> getRelations() {
        return this.relations;
    }

    @Override
    public String toString() {
        final StringBuilder sb = new StringBuilder();
        sb.append("Transition invariant: {\n");
        for (final TransitionRelation tr : this.relations) {
            sb.append(tr.toString());
        }
        sb.append("}");
        return sb.toString();
    }

    @Override
    public String export(final Export_Util eu) {
        final StringBuilder sb = new StringBuilder();
        sb.append(eu.bold(eu.tttext("Transition invariant:")));
        sb.append(eu.linebreak());
        for (final TransitionRelation tr : this.relations) {
            sb.append(tr.export(eu));
            sb.append(eu.linebreak());
        }
        return sb.toString();
    }
}
