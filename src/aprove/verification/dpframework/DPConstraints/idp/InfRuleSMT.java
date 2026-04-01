/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.DPConstraints.idp;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPConstraints.*;
import aprove.verification.dpframework.DPConstraints.Implication;
import aprove.verification.dpframework.DPConstraints.idp.InfRuleSMT.VarAnalysis.*;
import aprove.verification.dpframework.DPProblem.SMT_LIA.*;
import aprove.verification.dpframework.DPProblem.SMT_LIA.SMTLIB.*;
import aprove.verification.dpframework.IDPProblem.Processors.nonInf.*;
import aprove.verification.dpframework.IDPProblem.Processors.nonInf.poly.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Factories.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public abstract class InfRuleSMT extends InfRule {

    public static final BigInteger TWO = BigInteger.valueOf(2);

    protected final ISMTChecker smtEngine;

    public InfRuleSMT() {
        this.smtEngine = new YicesChecker();
    }

    protected Triple<Boolean, Map<GPolyVar, VarAnalysis>, Set<Set<MonomialAnalysis>>> analyzeImpl(
        final Implication implication,
        final IDPGInterpretation interpretation,
        final Abortion aborter) throws AbortionException
    {
        // System.err.println("ANALYZE " + implication);
        if (!this.isSolvable(implication.getConditions(), interpretation, aborter)) {
            return new Triple<Boolean, Map<GPolyVar, VarAnalysis>, Set<Set<MonomialAnalysis>>>(true, null, null);
        }

        //System.err.println("analyzeImpl " + implication);
        // System.out.println("processImpl " + implication);
        final Map<GPolyVar, VarAnalysis> varAnalysis = new LinkedHashMap<GPolyVar, VarAnalysis>();
        final Set<GPolyVar> variables = new LinkedHashSet<GPolyVar>();
        // collect all Variables
        for (final Constraint constraint : implication.getConditions()) {
            if (constraint.isPolyAtom()) {
                variables.addAll(((PolyAtom<BigIntImmutable>) constraint).getLhs().getVariables());
            }
        }

        if (implication.getConclusion().isConstraintSet()) {
            for (final Constraint constraint : (ConstraintSet) implication.getConclusion()) {
                if (constraint.isPolyAtom()) {
                    variables.addAll(((PolyAtom<BigIntImmutable>) constraint).getLhs().getVariables());
                }
            }
        } else {
            if (implication.getConclusion().isPolyAtom()) {
                variables.addAll(((PolyAtom<BigIntImmutable>) implication.getConclusion()).getLhs().getVariables());
            }
        }

        // create VarAnalysis
        for (final GPolyVar var : variables) {
            varAnalysis.put(var, new VarAnalysis(var, varAnalysis, interpretation.getRanges()));
        }

        // create monomial analysis and check which equations are useable
        final Map<Map.Entry<GMonomial<GPolyVar>, GPoly<BigIntImmutable, GPolyVar>>, MonomialAnalysis> monomials =
            new LinkedHashMap<Map.Entry<GMonomial<GPolyVar>, GPoly<BigIntImmutable, GPolyVar>>, MonomialAnalysis>();
        final Set<Set<MonomialAnalysis>> usable = new LinkedHashSet<Set<MonomialAnalysis>>();
        for (final Constraint constraint : implication.getConditions()) {
            // System.out.println("constraint " + constraint);
            if (aborter != null) {
                aborter.checkAbortion();
            }
            if (constraint.isPolyAtom()) {
                final PolyAtom<BigIntImmutable> atom = (PolyAtom<BigIntImmutable>) constraint;
                // might be invalid because of usable rules searched, can not count on this one
                // -> Extra UsableAtom...
                /*
                if ((atom.getULeft() != null && interpretation.isContextSensitive(atom.getLeft()))
                        || (atom.getURight() != null && interpretation.isContextSensitive(atom.getRight()))) {

                    continue;
                */
                // System.out.println("Atom: " + atom);
                if (!atom.getLhs().isFlat(interpretation.getPolyRing(), interpretation.getMonoid())) {
                    interpretation.getFvOuter().applyTo(atom.getLhs());
                }
                final ImmutableMap<GMonomial<GPolyVar>, GPoly<BigIntImmutable, GPolyVar>> atomMonoms =
                    atom.getLhs().getMonomials(interpretation.getPolyRing(), interpretation.getMonoid());
                // create VarAnalyis and MonomialAnalysis
                Set<MonomialAnalysis> atomMAnalysis = new LinkedHashSet<MonomialAnalysis>();
                final Set<GPolyVar> atomVars = new LinkedHashSet<GPolyVar>();
                // create monomial analysis
                for (final Map.Entry<GMonomial<GPolyVar>, GPoly<BigIntImmutable, GPolyVar>> entry : atomMonoms.entrySet()) {
                    MonomialAnalysis mAnalysis = monomials.get(entry);
                    if (mAnalysis == null) {
                        mAnalysis = new MonomialAnalysis(entry.getKey(), entry.getValue(), interpretation, varAnalysis);
                        monomials.put(entry, mAnalysis);
                    }
                    //System.err.println("mAnalysis.getCoeffSign() " + mAnalysis.getCoeffSign());
                    if (mAnalysis.getCoeffSign() != Signum.Wild) {
                        atomMAnalysis.add(mAnalysis);
                        atomVars.addAll(entry.getKey().getExponents().keySet());
                    } else {
                        atomMAnalysis = null;
                        break;
                    }
                }
                if (atomMAnalysis != null && !atomMAnalysis.isEmpty()) {
                    usable.add(atomMAnalysis);
                    // create split for variable
                    for (final GPolyVar var : atomVars) {
                        final MonomialSplit split = new MonomialSplit(atom, atom.getRelation());
                        for (final MonomialAnalysis mAnalysis : atomMAnalysis) {
                            if (mAnalysis.getProblemVars().contains(var)) {
                                split.getSolving().add(mAnalysis);
                            } else {
                                split.getNeeded().add(mAnalysis);
                            }
                        }
                        varAnalysis.get(var).getSolvingConstraints().add(split);
                    }
                }
            }
        }
        final Boolean contradiction = this.reanalyze(varAnalysis, usable, interpretation.isNat(), aborter).y;
        return new Triple<Boolean, Map<GPolyVar, VarAnalysis>, Set<Set<MonomialAnalysis>>>(
            contradiction,
            varAnalysis,
            usable);
    }

    /**
     *
     * @param varAnalysis
     * @param useable
     * @param isNat
     * @return res.x = changed, res.y = contradiction
     * @throws AbortionException
     */
    protected Pair<Boolean, Boolean> reanalyze(
        final Map<GPolyVar, VarAnalysis> varAnalysis,
        final Set<Set<MonomialAnalysis>> useable,
        final boolean isNat,
        final Abortion aborter) throws AbortionException
    {
        // do fix point iteration to determine problem variable signs
        boolean changed = true;
        boolean contradiction = false;
        boolean res = false;
        while (changed) {
            if (aborter != null) {
                aborter.checkAbortion();
            }
            changed = false;
            // reanalyze monomials
            for (final Set<MonomialAnalysis> atomMonomials : useable) {
                for (final MonomialAnalysis monom : atomMonomials) {
                    changed = monom.analyze() || changed;
                }
            }
            for (final VarAnalysis var : varAnalysis.values()) {
                changed = var.analyze() || changed;
                if (var.getSign() == Signum.Contradiction || (isNat && var.getSign() == Signum.StrictNeg)) {
                    // System.err.println("Contradiction in " + var);
                    var.analyze();
                    contradiction = true;
                }
            }
            /*
                        atoms:
                        for (Set<MonomialAnalysis> atomMonomials : currentUseable) {
                            GPolyVar currentVar = null;
                            int searchedVarSign = 0;
                            Integer searchedValSign = null;
                            for (MonomialAnalysis monom : atomMonomials) {
                                if (monom.getProblemVars().size() > 1) {
                                    currentUseable.remove(atomMonomials);
                                    continue atoms;
                                } else if (monom.getProblemVars().size() == 1) {
                                    if (currentVar == null) {
                                        currentVar = monom.getProblemVars().iterator().next();
                                        searchedVarSign = monom.getKnownVarSign() * monom.getCoeffSign();
                                    } else if (currentVar != monom.getProblemVars().iterator().next() ||
                                        searchedVarSign != monom.getKnownVarSign() * monom.getCoeffSign()) {
                                        currentUseable.remove(atomMonomials);
                                        continue atoms;
                                    }
                                } else {
                                    if (searchedValSign == null || searchedValSign == 0) {
                                        searchedValSign = monom.getSign();
                                    } else if (searchedValSign != monom.getSign()) {
                                        currentUseable.remove(atomMonomials);
                                        continue atoms;
                                    }
                                }
                            }
                            if (currentVar != null) {
                                problemVariables.get(currentVar).setSign(searchedValSign * -1);
                                changed = true;
                                break atoms;
                            }
                        }
            */
            if (changed) {
                res = true;
            }
        }
        return new Pair<Boolean, Boolean>(res, contradiction);
    }

    protected static class EvaluatedNode {

        private float evaluation;

        public float getEvaluation() {
            return this.evaluation;
        }

        public void setEvaluation(final float evaluation) {
            this.evaluation = evaluation;
        }

    }

    protected static enum Signum {
        Pos(1, "Pos"), StrictPos(2, "StrictPos"), Neg(-1, "Neg"), StrictNeg(-2, "StrictNeg"), Zero(0, "Zero"), Unknown(
            null,
            "Unknown"), Wild(null, "Wild"), Contradiction(null, "Contradiction");

        private final Integer id;
        private final String name;

        Signum(final Integer id, final String name) {
            this.id = id;
            this.name = name;
        }

        public Integer getId() {
            return this.id;
        }

        public boolean isStrict() {
            return this == StrictPos || this == StrictNeg;
        }

        public boolean isPos() {
            return this == Pos | this == StrictPos;
        }

        public boolean isNeg() {
            return this == Neg | this == StrictNeg;
        }

        /**
         * @param other other signum
         * @return true iff the two signums are compatible
         */
        public boolean isCompatible(final Signum other) {
            if (this == Unknown || other == Unknown) {
                return true;
            } else if (this == Contradiction || other == Contradiction) {
                return false;
            } else if (this == Wild || other == Wild) {
                return this == other;
            } else if (this == Pos) {
                return other.id >= -1;
            } else if (this == StrictPos) {
                return other.id > 0;
            } else if (this == Neg) {
                return other.id <= 1;
            } else if (this == StrictNeg) {
                return other.id < 0;
            } else if (this == Zero) {
                return other.id <= 1 && other.id >= -1;
            }
            throw new UnsupportedOperationException("unhandled combination");
        }

        /**
         * Use this method to determine the more specific signum from two neg or two pos signums,
         * e.g. for Pos and StrictPos
         * @param other the other Signum
         * @return
         */
        public Signum moreSpecific(final Signum other) {
            if (this == Contradiction || other == Contradiction) {
                return Contradiction;
            }
            ;
            if (this == Zero || other == Zero) {
                return Zero;
            } else if (this == Unknown) {
                return other;
            } else if (other == Unknown) {
                return this;
            } else if (this == Wild || other == Wild) {
                return Wild;
            }
            if ((this.id < 1 && other.id > 1) || (this.id > 1 && other.id < 1)) {
                throw new IllegalArgumentException("operation not allowed pos and neg");
            }
            if ((this.id > 0 && other.id < 0) || (this.id < 0 && other.id > 0)) {
                return Zero;
            }
            if (this.id > 0) {
                if (other.id > this.id) {
                    return other;
                } else {
                    return this;
                }
            } else {
                if (other.id < this.id) {
                    return other;
                } else {
                    return this;
                }
            }
        }

        public Signum mult(final Signum other) {
            if (this == Contradiction || other == Contradiction) {
                return Contradiction;
            } else if (this == Zero || other == Zero) {
                return Zero;
            } else if (this == Unknown || other == Unknown) {
                return Unknown;
            } else if (this == Wild || other == Wild) {
                return Wild;
            } else {
                switch (this.id.intValue() * other.id.intValue()) {
                case 1:
                    return Pos;
                case 2:
                    return Pos;
                case 4:
                    return StrictPos;
                case -1:
                    return Neg;
                case -2:
                    return Neg;
                case -4:
                    return StrictNeg;
                }
            }
            throw new UnsupportedOperationException("check mult procedure");
        }

        public Signum add(final Signum other) {
            if (this == Contradiction || other == Contradiction) {
                return Contradiction;
            } else if (this == Zero) {
                return other;
            } else if (other == Zero) {
                return this;
            } else if (this == Wild || other == Wild) {
                return Wild;
            } else if (this == Unknown || other == Unknown) {
                return Unknown;
            } else {
                if (!this.isCompatible(other)) {
                    return Wild;
                } else {
                    if (this == StrictPos || this == StrictNeg) {
                        return this;
                    } else {
                        return other;
                    }
                }
            }
        }

        @Override
        public String toString() {
            return this.name;
        }
    }

    public static class MonomialAnalysis extends EvaluatedNode {

        private final GPoly<BigIntImmutable, GPolyVar> coeff;
        private final GMonomial<GPolyVar> monomial;
        private final GInterpretation<BigIntImmutable> interpretation;
        private final Map<GPolyVar, VarAnalysis> variables;
        private Set<GPolyVar> problemVars;
        private Signum sign;
        private Signum coeffSign;
        private Signum knownVarSign;

        protected MonomialAnalysis(
            final GMonomial<GPolyVar> monomial,
            final GPoly<BigIntImmutable, GPolyVar> coeff,
            final GInterpretation<BigIntImmutable> interpretation,
            final Map<GPolyVar, VarAnalysis> variables)
        {
            this.coeff = coeff;
            this.monomial = monomial;
            this.interpretation = interpretation;
            this.variables = variables;
            this.sign = Signum.Unknown;
            this.coeffSign = Signum.Unknown;
            this.knownVarSign = Signum.Unknown;
            this.analyzeCoeff();
            if (variables != null) {
                this.analyze();
            }
        }

        /**
         * Analyzes the sign of the coefficient. Note that we we only allow pos coeff vars
         */
        protected void analyzeCoeff() {
            if (this.coeffSign == Signum.Unknown) {
                Signum newSign = Signum.Zero;
                if (!this.coeff.isFlat(this.interpretation.getRing(), this.interpretation.getMonoid())) {
                    this.interpretation.getFvInner().applyTo(this.coeff);
                }
                final ImmutableMap<GMonomial<GPolyVar>, BigIntImmutable> cMonoms =
                    this.coeff.getMonomials(this.interpretation.getRing(), this.interpretation.getMonoid());
                outer: for (final Map.Entry<GMonomial<GPolyVar>, BigIntImmutable> cMonom : cMonoms.entrySet()) {
                    int compare = cMonom.getValue().getBigInt().signum();
                    if (compare != 0) {
                        if (newSign != Signum.Zero && compare != Integer.signum(newSign.getId())) {
                            newSign = Signum.Wild;
                            break outer;
                        }
                        for (final Map.Entry<GPolyVar, BigInteger> var : cMonom.getKey().getExponents().entrySet()) {
                            if (var.getKey() instanceof NonInfBound && var.getValue().mod(InfRuleSMT.TWO).signum() != 0) {
                                compare *= -1;
                            } else if (var.getKey() instanceof NonInfArbitraryConstant) {
                                newSign = Signum.Wild;
                                break outer;
                            }
                        }
                        if (cMonom.getKey().getExponents().size() == 0) {
                            // constant part
                            if (compare > 0) {
                                newSign = Signum.StrictPos;
                            } else {
                                newSign = Signum.StrictNeg;
                            }
                        } else if (newSign == Signum.Zero) {
                            if (compare > 0) {
                                newSign = Signum.Pos;
                            } else {
                                newSign = Signum.Neg;
                            }
                        }
                    }
                }
                this.coeffSign = newSign;
            }
        }

        /**
         * Analyzes which variables are needed to determine the sign of the monomial and are not yet determined in their sign.
         * If no such variables exist and the sign of the coeff is known the sign of the monomial is determined
         * If the sign of the coeff is unknown, no variables are needed since the sign of the monomial can never be determined.
         * @return true iff if any changes since the last call to analyze occured
         */
        public boolean analyze() {
            if (aprove.Globals.useAssertions) {
                assert (this.variables != null);
            }
            final Set<GPolyVar> oldProblemVars = this.problemVars;
            final Signum oldSign = this.sign;
            this.problemVars = new LinkedHashSet<GPolyVar>();
            this.knownVarSign = Signum.Pos; // neutral element
            for (final Map.Entry<GPolyVar, BigInteger> exponent : this.monomial.getExponents().entrySet()) {
                if (exponent.getValue().mod(InfRuleSMT.TWO).compareTo(BigInteger.ZERO) != 0) {
                    final VarAnalysis varAnalysis = this.variables.get(exponent.getKey());
                    if (varAnalysis == null || varAnalysis.getSign() == null) {
                        this.problemVars.add(exponent.getKey());
                        this.knownVarSign = Signum.Unknown;
                    } else {
                        this.knownVarSign = this.knownVarSign.mult(varAnalysis.getSign());
                        if (this.knownVarSign == Signum.Zero) {
                            this.problemVars.clear();
                            break;
                        }
                    }
                }
            }
            if (this.knownVarSign == Signum.Zero || (this.problemVars.size() == 0 && this.coeffSign != Signum.Unknown)) {
                this.sign = this.knownVarSign.mult(this.coeffSign);
            } else {
                this.sign = Signum.Unknown;
            }
            return oldProblemVars == null
                || oldSign == null
                || !this.problemVars.equals(oldProblemVars)
                || !this.sign.equals(oldSign);
        }

        public GMonomial<GPolyVar> getMonomial() {
            return this.monomial;
        }

        public Map<GPolyVar, VarAnalysis> getVariables() {
            return this.variables;
        }

        public Set<GPolyVar> getProblemVars() {
            return this.problemVars;
        }

        public GPoly<BigIntImmutable, GPolyVar> getCoeff() {
            return this.coeff;
        }

        public Signum getSign() {
            return this.sign;
        }

        public Signum getCoeffSign() {
            return this.coeffSign;
        }

        public Signum getKnownVarSign() {
            return this.knownVarSign;
        }

        public Signum getKnownVarSign(final GPolyVar exceptVar) {
            Signum sign = Signum.Pos; // neutral element
            for (final Map.Entry<GPolyVar, BigInteger> exponent : this.monomial.getExponents().entrySet()) {
                if (exceptVar != null && exponent.getKey().equals(exceptVar)) {
                    continue;
                }
                if (exponent.getValue().mod(InfRuleSMT.TWO).compareTo(BigInteger.ZERO) != 0) {
                    final VarAnalysis varAnalysis = this.variables.get(exponent.getKey());
                    if (varAnalysis != null && varAnalysis.getSign() != null) {
                        sign = sign.mult(varAnalysis.getSign());
                        if (sign == Signum.Zero) {
                            break;
                        }
                    } else {
                        sign = Signum.Unknown;
                        break;
                    }
                }
            }
            return sign;
        }

        @Override
        public int hashCode() {
            return this.monomial.hashCode();
        }

        @Override
        public boolean equals(final Object other) {
            return this.monomial.equals(other);
        }

        @Override
        public String toString() {
            return "MonomialAnalysis "
                + this.monomial
                + ": sign "
                + this.sign
                + ", coeffSign "
                + this.coeffSign
                + ", knownVarSign "
                + this.knownVarSign;
        }
    }

    protected static class VarAnalysis extends EvaluatedNode {

        private final GPolyVar var;
        private final Set<MonomialSplit> solvingConstraints;
        private Signum sign;
        private Signum fixSign;
        private final Map<GPolyVar, VarAnalysis> varAnalysis;
        private final Map<GPolyVar, OPCRange<BigIntImmutable>> ranges;

        protected VarAnalysis(
            final GPolyVar var,
            final Map<GPolyVar, VarAnalysis> varAnalysis,
            final Map<GPolyVar, OPCRange<BigIntImmutable>> ranges)
        {
            this.var = var;
            this.varAnalysis = varAnalysis;
            this.ranges = ranges;
            this.solvingConstraints = new LinkedHashSet<MonomialSplit>();
            this.fixSign = Signum.Unknown;
        }

        public boolean analyze() {
            if (this.sign == Signum.Zero) {
                return false;
            }
            final Signum oldSign = this.sign;
            this.sign = this.fixSign;
            final Iterator<MonomialSplit> constraintIterator = this.solvingConstraints.iterator();
            // System.out.println("VarAnalysis ana: " + var + " " + solvingConstraints.size());
            //System.err.println("VarAnalysis " + var + " " + solvingConstraints.size());

            outer: while (constraintIterator.hasNext()) {
                final MonomialSplit split = constraintIterator.next();
                // System.out.println("VarAnalysis: " + var + " " + split);
                Signum searchedSig = null;
                // analyze solving monomials, all coeff + other vars must have same signum
                final Iterator<MonomialAnalysis> solvingIterator = split.getSolving().iterator();
                while (solvingIterator.hasNext()) {
                    final MonomialAnalysis solving = solvingIterator.next();
                    final Signum solvingSig = solving.getCoeffSign().mult(solving.getKnownVarSign(this.var));
                    if (solvingSig == Signum.Zero) {
                        solvingIterator.remove();
                        continue;
                    } else if (solvingSig == Signum.Unknown) {
                        continue outer;
                    } else if (solvingSig == Signum.Wild) {
                        constraintIterator.remove();
                        continue outer;
                    }

                    // we need all coeff signums pos or all neg otherwise constraint is wild in x
                    if (searchedSig == null || searchedSig.isCompatible(solvingSig)) {
                        if (searchedSig == null) {
                            searchedSig = solvingSig;
                        } else {
                            if (Globals.useAssertions) {
                                assert (solvingSig.moreSpecific(searchedSig) == searchedSig.moreSpecific(solvingSig));
                            }
                            searchedSig = searchedSig.moreSpecific(solvingSig);
                        }
                    } else {
                        constraintIterator.remove();
                        continue outer;
                    }
                }
                //System.err.println("searchedSig: " + var + " " + searchedSig);
                if (searchedSig == null) {
                    // no solved monomial with strict known signum
                    continue outer;
                }
                // analyze needed monomials, must all be <= 0
                boolean strict = false;
                final Iterator<MonomialAnalysis> neededIterator = split.getNeeded().iterator();
                while (neededIterator.hasNext()) {
                    final MonomialAnalysis needed = neededIterator.next();
                    final Signum neededSign = needed.getSign();
                    //System.err.println("    neededSign: " + needed.monomial + " "+ needed.coeff + " " + neededSign);
                    if (neededSign == Signum.Zero) {
                        neededIterator.remove();
                        continue;
                    } else if (neededSign == Signum.Unknown) {
                        continue outer;
                    } else if (neededSign == Signum.Wild
                        || neededSign == Signum.Contradiction
                        || neededSign.getId() > 0)
                    {
                        constraintIterator.remove();
                        continue outer;
                    }
                    if (neededSign == Signum.StrictNeg) {
                        strict = true;
                    }
                }
                Signum newSign;
                if (searchedSig.isPos()) {
                    if (strict && searchedSig.isStrict()) {
                        newSign = Signum.StrictPos;
                    } else {
                        newSign = Signum.Pos;
                    }
                } else {
                    if (strict && searchedSig.isStrict()) {
                        newSign = Signum.StrictNeg;
                    } else {
                        newSign = Signum.Neg;
                    }
                }
                //System.err.println("new Sign " + newSign + " (" + sign + ")");

                if (this.sign.isCompatible(newSign)) {
                    if (Globals.useAssertions) {
                        assert (this.sign.moreSpecific(newSign) == newSign.moreSpecific(this.sign));
                    }
                    this.sign = this.sign.moreSpecific(newSign);
                } else {
                    this.sign = Signum.Contradiction;
                    break outer;
                }
            }
            final OPCRange<BigIntImmutable> range = this.ranges.get(this.var);
            if (range != null) {
                Signum newSign = Signum.Unknown;
                final Pair<BigIntImmutable, BigIntImmutable> r = range.getList().get(0);
                final int xSign = r.x.getBigInt().signum();
                final int ySign = r.y.getBigInt().signum();
                if (xSign == 0 && ySign == 0) {
                    newSign = Signum.Zero;
                } else if (xSign > 0) {
                    newSign = Signum.StrictPos;
                } else if (xSign == 0) {
                    newSign = Signum.Pos;
                } else if (ySign < 0) {
                    newSign = Signum.StrictNeg;
                } else if (ySign == 0) {
                    newSign = Signum.Neg;
                }
                if (this.sign.isCompatible(newSign)) {
                    if (Globals.useAssertions) {
                        assert (this.sign.moreSpecific(newSign) == newSign.moreSpecific(this.sign));
                    }
                    this.sign = this.sign.moreSpecific(newSign);
                } else {
                    this.sign = Signum.Contradiction;
                }
            }
            return oldSign != this.sign;
        }

        public GPolyVar getVar() {
            return this.var;
        }

        public Set<MonomialSplit> getSolvingConstraints() {
            return this.solvingConstraints;
        }

        @Override
        public int hashCode() {
            return this.var.hashCode();
        }

        @Override
        public boolean equals(final Object other) {
            return this.var.equals(other);
        }

        public Signum getSign() {
            return this.sign;
        }

        public Signum getFixSign() {
            return this.fixSign;
        }

        public void setFixSign(final Signum fixSign) {
            this.fixSign = fixSign;
        }

        public void setSign(final Signum sign) {
            this.sign = sign;
        }

        @Override
        public String toString() {
            return "VarAnalysis " + this.var + ": " + this.sign;
        }

        public static class MonomialSplit {

            private final Set<MonomialAnalysis> solving;
            private final Set<MonomialAnalysis> needed;
            private final ConstraintType relation;
            public final PolyAtom<BigIntImmutable> constraint;

            public MonomialSplit(final PolyAtom<BigIntImmutable> constraint, final ConstraintType relation) {
                this.solving = new LinkedHashSet<MonomialAnalysis>();
                this.needed = new LinkedHashSet<MonomialAnalysis>();
                ;
                this.relation = relation;
                this.constraint = constraint;
            }

            public Set<MonomialAnalysis> getSolving() {
                return this.solving;
            }

            public Set<MonomialAnalysis> getNeeded() {
                return this.needed;
            }

            public ConstraintType getRelation() {
                return this.relation;
            }

            @Override
            public String toString() {
                return "MonomialSplit solving: " + this.solving + ", needed: " + this.needed;
            }
        }

    }

    protected boolean isSolvable(
        final Set<? extends Constraint> conds,
        final IDPGInterpretation interpretation,
        final Abortion aborter) throws AbortionException
    {
        if (conds.isEmpty()) {
            return true;
        }

        final List<ImmutableBoolOp<LIAConstraint>> constraints = new ArrayList<ImmutableBoolOp<LIAConstraint>>(conds.size());
        final GPolyFactory<BigIntImmutable, GPolyVar> innerFactory = interpretation.getFactory().getInnerFactory();
        condFor: for (final Constraint constraint : conds) {
            if (constraint.isPolyAtom()) {
                final PolyAtom<BigIntImmutable> atom = ((PolyAtom<BigIntImmutable>) constraint);
                final GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> poly = atom.getLhs();
                if (!poly.isFlat(interpretation.getFvOuter().getRingC(), interpretation.getFvOuter().getMonoid())) {
                    interpretation.getFvOuter().applyTo(poly);
                }
                GPoly<BigIntImmutable, GPolyVar> res = null;
                for (final Map.Entry<GMonomial<GPolyVar>, GPoly<BigIntImmutable, GPolyVar>> monomial : poly.getMonomials(
                    interpretation.getPolyRing(),
                    interpretation.getMonoid()).entrySet())
                {
                    final Map<GPolyVar, BigInteger> exponents = monomial.getKey().getExponents();
                    // not linear in outer variables?
                    if (exponents.size() == 1) {
                        if (exponents.values().iterator().next().compareTo(BigInteger.ONE) == 1) {
                            continue condFor;
                        }
                    }
                    if (exponents.size() > 1) {
                        continue condFor;
                    }
                    GPoly<BigIntImmutable, GPolyVar> coeff = monomial.getValue();
                    if (exponents.size() > 0) {
                        if (!coeff.isFlat(interpretation.getFvInner().getRingC(), interpretation
                            .getFvInner()
                            .getMonoid()))
                        {
                            interpretation.getFvInner().applyTo(coeff);
                        }
                        if (coeff.containsVariable()) {
                            continue condFor;
                        }
                        final BigIntImmutable coeffConstant =
                            coeff.getConstantPart(interpretation.getRing(), interpretation.getMonoid());
                        coeff =
                            innerFactory.concat(
                                coeffConstant,
                                innerFactory.buildVariable(exponents.keySet().iterator().next()));
                    }
                    if (res == null) {
                        res = coeff;
                    } else {
                        res = innerFactory.plus(res, coeff);
                    }
                }
                if (res != null) {
                    interpretation.getFvInner().applyTo(res);
                    constraints.add(ImmutableBoolOp.createAtom(new LIAConstraint(res, interpretation
                        .getFactory()
                        .getInnerFactory()
                        .zero(), atom.getRelation() == ConstraintType.EQ
                        ? ArithmeticRelation.EQ
                            : ArithmeticRelation.GE)));
                }
            }
        }
        final YNM solution = this.smtEngine.isSatisfiable(ImmutableBoolOp.createConjunction(constraints), aborter);
        return solution != YNM.NO;
    }

}
