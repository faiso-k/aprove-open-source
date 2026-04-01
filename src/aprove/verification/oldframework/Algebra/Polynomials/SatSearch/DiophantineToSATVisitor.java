package aprove.verification.oldframework.Algebra.Polynomials.SatSearch;

import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

class DiophantineToSATVisitor implements FineGrainedFormulaVisitor<Formula<None>, Diophantine> {

    private final Map<Variable<Diophantine>, Variable<None>> varMapping;
    private final Map<Formula<Diophantine>, Formula<None>> visited;
    private final PoloSatConverter converter;
    private final FormulaFactory<None> factory;

    private DiophantineToSATVisitor(PoloSatConverter converter) {
        this.converter = converter;
        this.factory = converter.getPropFactory();
        this.visited = new HashMap<Formula<Diophantine>, Formula<None>>();
        this.varMapping = new HashMap<Variable<Diophantine>, Variable<None>>();
    }

    public static DiophantineToSATVisitor create(PoloSatConverter converter) {
        return new DiophantineToSATVisitor(converter);
    }

    @Override
    public Formula<None> get(Formula<Diophantine> f) {
        return this.visited.get(f);
    }

    @Override
    public Formula<None> outAnd(AndFormula<Diophantine> f, List<Formula<None>> l) {
        Formula<None> result = this.factory.buildAnd(l);
        this.visited.put(f, result);
        return result;
    }

    @Override
    public Formula<None> outConstant(Constant<Diophantine> f) {
        boolean value = f.getValue();
        return this.factory.buildConstant(value);
    }

    @Override
    public Formula<None> outIff(IffFormula<Diophantine> f, Formula<None> g1, Formula<None> g2) {
        Formula<None> result = this.factory.buildIff(g1, g2);
        this.visited.put(f, result);
        return result;
    }

    @Override
    public Formula<None> outIte(IteFormula<Diophantine> f, Formula<None> g1,
            Formula<None> g2, Formula<None> g3) {
        Formula<None> result = this.factory.buildIte(g1, g2, g3);
        this.visited.put(f, result);
        return result;
    }

    @Override
    public Formula<None> outNot(NotFormula<Diophantine> f, Formula<None> g) {
        Formula<None> result = this.factory.buildNot(g);
        this.visited.put(f, result);
        return result;
    }

    @Override
    public Formula<None> outOr(OrFormula<Diophantine> f, List<Formula<None>> l) {
        Formula<None> result = this.factory.buildOr(l);
        this.visited.put(f, result);
        return result;
    }

    @Override
    public Formula<None> outTheoryAtom(TheoryAtom<Diophantine> f) {
        Diophantine dio = f.getProposition();
        Formula<None> result = this.converter.convertDiophantine(dio);
        this.visited.put(f, result);
        return result;
    }

    @Override
    public Formula<None> outVariable(Variable<Diophantine> f) {
        Variable<None> res = this.varMapping.get(f);
        if (res == null) {
            res = this.factory.buildVariable();
            this.varMapping.put(f, res);
            this.visited.put(f, res);
        }
        return res;
    }

    @Override
    public Formula<None> outXor(XorFormula<Diophantine> f, List<Formula<None>> l) {
        Formula<None> result = this.factory.buildXor(l);
        this.visited.put(f, result);
        return result;
    }

    public Map<Variable<Diophantine>, Variable<None>> getVarMapping() {
        return this.varMapping;
    }

    @Override
    public Formula<None> outAtLeast(AtLeastFormula<Diophantine> f,
            List<Formula<None>> l) {
        int cardinality = f.getCardinality();
        Formula<None> result = this.factory.buildAtLeast(l, cardinality);
        this.visited.put(f, result);
        return result;
    }

    @Override
    public Formula<None> outAtMost(AtMostFormula<Diophantine> f,
            List<Formula<None>> l) {
        int cardinality = f.getCardinality();
        Formula<None> result = this.factory.buildAtMost(l, cardinality);
        this.visited.put(f, result);
        return result;
    }

    @Override
    public Formula<None> outCount(CountFormula<Diophantine> f,
            List<Formula<None>> l) {
        int cardinality = f.getCardinality();
        Formula<None> result = this.factory.buildCount(l, cardinality);
        this.visited.put(f, result);
        return result;
    }
}
