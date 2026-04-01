package aprove.verification.oldframework.PropositionalLogic.Formulae;

import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.*;

/**
 * converts formulas of T_SRC type into formulas of T_DEST type.
 * Here, if input formulas contain non-theory variables,
 * then one also needs to provide a mapping for variables (will be filled on demand)
 *
 * @author thiemann
 *
 * @param <T_SRC>
 * @param <T_DEST>
 */
public class TheoryConverterVisitor<T_SRC, T_DEST> implements FormulaVisitor<Formula<T_DEST>, T_SRC> {

    private FormulaFactory<T_DEST> factory;
    private TheoryConverter<T_SRC,T_DEST> converter;
    private Map<Variable<T_SRC>, Variable<T_DEST>> variableMapping;

    /**
     * Creates visitor which is not able to transform non-theory variables.
     * @param factory
     * @param converter
     */
    public TheoryConverterVisitor(
            FormulaFactory<T_DEST> factory,
            TheoryConverter<T_SRC, T_DEST> converter
            ) {
        this(factory, converter, null);
    }


    /**
     * @param factory
     * @param converter
     * @param variableMapping may be null, but then no variables may be seen, as it is unclear how they can
     *   be mapped. Otherwise, this map will be modified, such that it later contains all seen variable-conversions.
     */
    public TheoryConverterVisitor(
            FormulaFactory<T_DEST> factory,
            TheoryConverter<T_SRC, T_DEST> converter,
            Map<Variable<T_SRC>, Variable<T_DEST>> variableMapping
            ) {
        this.factory = factory;
        this.converter = converter;
        this.variableMapping = variableMapping;
    }

    @Override
    public Formula<T_DEST> caseAnd(AndFormula<T_SRC> f) {
        List<Formula<T_DEST>> args = new ArrayList<Formula<T_DEST>>(f.args.size());
        for (Formula<T_SRC> arg : f.args) {
            args.add(arg.apply(this));
        }
        return this.factory.buildAnd(args);
    }

    @Override
    public Constant<T_DEST> caseConstant(Constant<T_SRC> f) {
        return this.factory.buildConstant(f.getValue());
    }

    @Override
    public Formula<T_DEST> caseIff(IffFormula<T_SRC> f) {
        Formula<T_DEST> left = f.left.apply(this);
        Formula<T_DEST> right = f.right.apply(this);
        return this.factory.buildIff(left, right);
    }

    @Override
    public Formula<T_DEST> caseIte(IteFormula<T_SRC> f) {
        Formula<T_DEST> condition = f.condition.apply(this);
        Formula<T_DEST> thenFormula = f.thenFormula.apply(this);
        Formula<T_DEST> elseFormula = f.elseFormula.apply(this);
        return this.factory.buildIte(condition, thenFormula, elseFormula);
    }

    @Override
    public Formula<T_DEST> caseNot(NotFormula<T_SRC> f) {
        Formula<T_DEST> newF = f.arg.apply(this);
        return this.factory.buildNot(newF);
    }

    @Override
    public Formula<T_DEST> caseOr(OrFormula<T_SRC> f) {
        List<Formula<T_DEST>> args = new ArrayList<Formula<T_DEST>>(f.args.size());
        for (Formula<T_SRC> arg : f.args) {
            args.add(arg.apply(this));
        }
        return this.factory.buildOr(args);
    }

    @Override
    public Formula<T_DEST> caseTheoryAtom(TheoryAtom<T_SRC> f) {
        return this.converter.convert(f.getProposition());
    }

    @Override
    public Formula<T_DEST> caseVariable(Variable<T_SRC> f) {
        if (this.variableMapping == null) {
            throw new RuntimeException("Variables are not allowed if variable mapping is not provided");
        } else {
            Variable<T_DEST> v = this.variableMapping.get(f);
            if (v == null) {
                v = this.factory.buildVariable();
                this.variableMapping.put(f, v);
            }
            return v;
        }
    }

    @Override
    public Formula<T_DEST> caseXor(XorFormula<T_SRC> f) {
        List<Formula<T_DEST>> args = new ArrayList<Formula<T_DEST>>(f.args.size());
        for (Formula<T_SRC> arg : f.args) {
            args.add(arg.apply(this));
        }
        return this.factory.buildXor(args);
    }


    @Override
    public Formula<T_DEST> caseAtLeast(AtLeastFormula<T_SRC> f) {
        List<Formula<T_DEST>> args = new ArrayList<Formula<T_DEST>>(f.args.size());
        for (Formula<T_SRC> arg : f.args) {
            args.add(arg.apply(this));
        }
        return this.factory.buildAtLeast(args, f.cardinality);
    }


    @Override
    public Formula<T_DEST> caseAtMost(AtMostFormula<T_SRC> f) {
        List<Formula<T_DEST>> args = new ArrayList<Formula<T_DEST>>(f.args.size());
        for (Formula<T_SRC> arg : f.args) {
            args.add(arg.apply(this));
        }
        return this.factory.buildAtMost(args, f.cardinality);
    }


    @Override
    public Formula<T_DEST> caseCount(CountFormula<T_SRC> f) {
        List<Formula<T_DEST>> args = new ArrayList<Formula<T_DEST>>(f.args.size());
        for (Formula<T_SRC> arg : f.args) {
            args.add(arg.apply(this));
        }
        return this.factory.buildCount(args, f.cardinality);
    }
}
