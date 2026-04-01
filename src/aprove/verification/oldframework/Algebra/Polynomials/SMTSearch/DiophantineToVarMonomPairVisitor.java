package aprove.verification.oldframework.Algebra.Polynomials.SMTSearch;

import java.util.*;

import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

class DiophantineToVarMonomPairVisitor
        implements
        FineGrainedFormulaVisitor<Pair<Set<String>, Set<IndefinitePart>>, Diophantine> {

    private final Set<String> variables;
    private final Set<IndefinitePart> monoms;

    public DiophantineToVarMonomPairVisitor() {
        this.variables = new LinkedHashSet<String>();
        this.monoms = new LinkedHashSet<IndefinitePart>();
    }

    public Set<String> getVariables() {
        return this.variables;
    }

    public Set<IndefinitePart> getMonoms() {
        return this.monoms;
    }

    @Override
    public Pair<Set<String>, Set<IndefinitePart>> outAnd(
            AndFormula<Diophantine> f,
            List<Pair<Set<String>, Set<IndefinitePart>>> l) {
        for (Formula<Diophantine> arg : f.getArgs()) {
            Pair<Set<String>, Set<IndefinitePart>> pair = arg.apply(this);
            this.monoms.addAll(pair.y);
            this.variables.addAll(pair.x);
        }
        Pair<Set<String>, Set<IndefinitePart>> result = new Pair<Set<String>, Set<IndefinitePart>>(
                this.variables, this.monoms);
        return result;
    }

    @Override
    public Pair<Set<String>, Set<IndefinitePart>> outConstant(
            Constant<Diophantine> f) {
        Pair<Set<String>, Set<IndefinitePart>> result = new Pair<Set<String>, Set<IndefinitePart>>(
                this.variables, this.monoms);
        return result;
    }

    @Override
    public Pair<Set<String>, Set<IndefinitePart>> outIff(
            IffFormula<Diophantine> f,
            Pair<Set<String>, Set<IndefinitePart>> g1,
            Pair<Set<String>, Set<IndefinitePart>> g2) {
        Set<String> a = new LinkedHashSet<String>(g1.x);
        a.addAll(g2.x);
        Set<IndefinitePart> b = new LinkedHashSet<IndefinitePart>(g1.y);
        b.addAll(g2.y);
        Pair<Set<String>, Set<IndefinitePart>> result = new Pair<Set<String>, Set<IndefinitePart>>(
                a, b);
        return result;
    }

    @Override
    public Pair<Set<String>, Set<IndefinitePart>> outIte(
            IteFormula<Diophantine> f,
            Pair<Set<String>, Set<IndefinitePart>> g1,
            Pair<Set<String>, Set<IndefinitePart>> g2,
            Pair<Set<String>, Set<IndefinitePart>> g3) {
        Set<String> a = new LinkedHashSet<String>(g1.x);
        a.addAll(g2.x);
        a.addAll(g3.x);

        Set<IndefinitePart> b = new LinkedHashSet<IndefinitePart>(g1.y);
        b.addAll(g2.y);
        b.addAll(g3.y);
        Pair<Set<String>, Set<IndefinitePart>> result = new Pair<Set<String>, Set<IndefinitePart>>(
                a, b);
        return result;
    }

    @Override
    public Pair<Set<String>, Set<IndefinitePart>> outNot(
            NotFormula<Diophantine> f, Pair<Set<String>, Set<IndefinitePart>> g) {
        Set<String> a = new LinkedHashSet<String>(g.x);
        Set<IndefinitePart> b = new LinkedHashSet<IndefinitePart>(g.y);
        Pair<Set<String>, Set<IndefinitePart>> result = new Pair<Set<String>, Set<IndefinitePart>>(
                a, b);
        return result;
    }

    @Override
    public Pair<Set<String>, Set<IndefinitePart>> outOr(
            OrFormula<Diophantine> f,
            List<Pair<Set<String>, Set<IndefinitePart>>> l) {
        for (Formula<Diophantine> arg : f.getArgs()) {
            Pair<Set<String>, Set<IndefinitePart>> pair = arg.apply(this);
            this.monoms.addAll(pair.y);
            this.variables.addAll(pair.x);
        }
        Pair<Set<String>, Set<IndefinitePart>> result = new Pair<Set<String>, Set<IndefinitePart>>(
                this.variables, this.monoms);
        return result;
    }

    @Override
    public Pair<Set<String>, Set<IndefinitePart>> outTheoryAtom(
            TheoryAtom<Diophantine> f) {
        SimplePolynomial dio = f.getProposition().getLeft().minus(
                f.getProposition().getRight());
        Set<String> a = new LinkedHashSet<String>(dio
                .getIndefinites());
        Set<IndefinitePart> b = new LinkedHashSet<IndefinitePart>();
        for (IndefinitePart indef : dio.getSimpleMonomials().keySet()) {
            if (indef.isIndefinite() || !indef.isLinear()) {
                b.add(indef);
            }
        }
        this.variables.addAll(a);
        this.monoms.addAll(b);
        Pair<Set<String>, Set<IndefinitePart>> result = new Pair<Set<String>, Set<IndefinitePart>>(
                a, b);
        return result;
    }

    @Override
    public Pair<Set<String>, Set<IndefinitePart>> outVariable(
            Variable<Diophantine> f) {
        return null;
    }

    @Override
    public Pair<Set<String>, Set<IndefinitePart>> outAtLeast(
            AtLeastFormula<Diophantine> f,
            List<Pair<Set<String>, Set<IndefinitePart>>> l) {
        return null;
    }

    @Override
    public Pair<Set<String>, Set<IndefinitePart>> outAtMost(
            AtMostFormula<Diophantine> f,
            List<Pair<Set<String>, Set<IndefinitePart>>> l) {
        return null;
    }

    @Override
    public Pair<Set<String>, Set<IndefinitePart>> outCount(
            CountFormula<Diophantine> f,
            List<Pair<Set<String>, Set<IndefinitePart>>> l) {
        return null;
    }

    @Override
    public Pair<Set<String>, Set<IndefinitePart>> get(Formula<Diophantine> f) {
        return null;
    }

    @Override
    public Pair<Set<String>, Set<IndefinitePart>> outXor(
            XorFormula<Diophantine> f,
            List<Pair<Set<String>, Set<IndefinitePart>>> l) {
        return null;
    }
}
