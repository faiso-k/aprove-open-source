package aprove.verification.dpframework.Orders.SAT;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.Variable;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.PropositionalLogic.ValueCaches.*;

public class SUBEncoder {

    private FormulaFactory<None> formulaFactory;
    private FactFactory factFactory;
    private SATPatterns<None> patterns;
    private Constant<None> ZERO;
    private Constant<None> ONE;
    private SUB sub;
    private Set<FunctionSymbol> headSyms;

    public SUBEncoder(FormulaFactory<None> formulaFactory, Set<FunctionSymbol> headSyms, SUB sub) {
        this.sub = sub;
        this.headSyms = headSyms;
        this.formulaFactory = formulaFactory;
        this.ZERO = formulaFactory.buildConstant(false);
        this.ONE = formulaFactory.buildConstant(true);
        this.factFactory = new FactFactory(formulaFactory);
        this.patterns = new SATPatterns<None>(formulaFactory, true);
    }

    public Formula<None> encode(Set<Rule> P, boolean allStrict, Abortion aborter) throws AbortionException {
        ValueCache<None> knownValues = new NoValueCache<None>(this.formulaFactory);
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        args.add(this.encodeGlobalConstraints(knownValues));
        if (allStrict) {
            args.add(this.encodeAllGreater(P, knownValues, aborter));
        } else {
            args.add(this.encodeAllGreaterEqual(P, knownValues, aborter));
            args.add(this.encodeOneGreater(P, knownValues, aborter));
        }
        Formula<None> formula = this.formulaFactory.buildAnd(args);
        return formula;
    }

    public Formula<None> encodeGlobalConstraints(ValueCache<None> knownValues) {
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        for (FunctionSymbol f : this.headSyms) {
            int arity = f.getArity();
            if (arity == 0) {
                args.add(this.factFactory.getVarFlag(f));
            } else {
                args.add(this.factFactory.getNotFlag(f));
                args.add(this.patterns.encodeExactlyOne(this.factFactory.getVarArgs(f)));
            }
        }
        Formula<None> formula = this.formulaFactory.buildAnd(args);
        knownValues.update(formula);
        return formula;
    }

    private Formula<None> encodeAllGreaterEqual(Set<Rule> rules, ValueCache<None> knownValues, Abortion aborter) throws AbortionException {
        if (rules.size() == 1) {
            Rule rule = rules.iterator().next();
            Formula<None> formula = this.encodeRule(rule.getLeft(), rule.getRight(), OrderRelation.GE, knownValues);
            knownValues.update(formula);
            return formula;
        }
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        for (Rule rule : rules) {
            aborter.checkAbortion();
            Formula<None> formula = this.encodeRule(rule.getLeft(), rule.getRight(), OrderRelation.GE, knownValues);
            if (formula == this.ZERO) {
                return formula;
            }
            knownValues.update(formula);
            args.add(formula);
        }
        return this.formulaFactory.buildAnd(args);
    }

    private Formula<None> encodeAllGreater(Set<Rule> rules, ValueCache<None> knownValues, Abortion aborter) throws AbortionException {
        if (rules.size() == 1) {
            Rule rule = rules.iterator().next();
            Formula<None> formula = this.encodeRule(rule.getLeft(), rule.getRight(), OrderRelation.GR, knownValues);
            knownValues.update(formula);
            return formula;
        }
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        for (Rule rule : rules) {
            aborter.checkAbortion();
            Formula<None> formula = this.encodeRule(rule.getLeft(), rule.getRight(), OrderRelation.GR, knownValues);
            if (formula == this.ZERO) {
                return formula;
            }
            knownValues.update(formula);
            args.add(formula);
        }
        return this.formulaFactory.buildAnd(args);
    }

    private Formula<None> encodeOneGreater(Set<Rule> rules, ValueCache<None> knownValues, Abortion aborter) throws AbortionException {
        if (rules.size() == 1) {
            Rule rule = rules.iterator().next();
            return this.encodeRule(rule.getLeft(), rule.getRight(), OrderRelation.GR, knownValues);
        }
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        for (Rule rule : rules) {
            aborter.checkAbortion();
            Formula<None> formula = this.encodeRule(rule.getLeft(), rule.getRight(), OrderRelation.GR, knownValues);
            if (formula == this.ONE) {
                return formula;
            }
            args.add(formula);
        }
        return this.formulaFactory.buildOr(args);
    }

    private Formula<None> encodeRule(TRSTerm s, TRSTerm t, OrderRelation rel, ValueCache<None> knownValues) {
        if (!s.isVariable()) {
            TRSFunctionApplication fApp = (TRSFunctionApplication) s;
            FunctionSymbol f = fApp.getRootSymbol();
            int fArity = f.getArity();
            // maybe f is collapsing
            if (fArity > 0 && this.headSyms.contains(f)) {
                List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
                for (int i = 0 ; i < fArity; i++) {
                    Variable<None> varFArgI = this.factFactory.getVarArg(f, i);
                    Formula<None> eVarFArgI = varFArgI.evaluate(knownValues);
                    if (eVarFArgI != this.ZERO) {
                        Formula<None> subFormula = this.encodeRule(fApp.getArgument(i),t,rel,knownValues);
                        dArgs.add(this.formulaFactory.buildAnd(eVarFArgI, subFormula));
                    }
                }
                return this.formulaFactory.buildOr(dArgs);
            }
        }
        if (!t.isVariable()) {
            TRSFunctionApplication gApp = (TRSFunctionApplication) t;
            FunctionSymbol g = gApp.getRootSymbol();
            int gArity = g.getArity();
            // maybe g is collapsing
            if (gArity > 0 && this.headSyms.contains(g)) {
                List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
                for (int j = 0 ; j < gArity; j++) {
                    Variable<None> varGArgJ = this.factFactory.getVarArg(g, j);
                    Formula<None> eVarGArgJ = varGArgJ.evaluate(knownValues);
                    if (eVarGArgJ != this.ZERO) {
                        Formula<None> subFormula = this.encodeRule(s,gApp.getArgument(j),rel,knownValues);
                        dArgs.add(this.formulaFactory.buildAnd(eVarGArgJ, subFormula));
                    }
                }
                return this.formulaFactory.buildOr(dArgs);
            }
        }
        // f and g are not collapsing -> equality is syntactic
        return this.sub.solves(Constraint.create(s, t, rel)) ? this.ONE : this.ZERO;
    }

    public Set<Variable<None>> decode(int[] res, int maxUsedVarId) {
        Set<Integer> isTrue = new LinkedHashSet<Integer>();
        int end = res.length;
        if (maxUsedVarId < res.length) {
            end = maxUsedVarId;
        }
        for (int i = 0; i < end; i++) {
            int value = res[i];
            if (value > 0) {
                isTrue.add(value);
            }
        }
        Set<Variable<None>> knownTrue = new LinkedHashSet<Variable<None>>();
        for (Variable<None> var : this.factFactory.getFactMap().keySet()) {
            if (isTrue.contains(var.getId())) {
                knownTrue.add(var);
            }
        }
        return knownTrue;
    }

    public Afs getAfs(Set<Variable<None>> knownTrue) {
        Afs afs = new Afs();
        for (FunctionSymbol f : this.headSyms) {
            int arity = f.getArity();
            Variable[] varArgs = this.factFactory.getVarArgs(f);
            if (knownTrue.contains(this.factFactory.getVarFlag(f))) {
                // f is non-collapsing
                YNM[] args = new YNM[arity];
                for (int i = 0; i < arity; i++) {
                    args[i] = knownTrue.contains(varArgs[i]) ? YNM.YES : YNM.NO;
                }
                afs.setFiltering(f, args);
            } else {
                // f is collapsing
                for (int i = 0; i < arity; i++) {
                    if (knownTrue.contains(varArgs[i])) {
                        afs.setCollapsing(f,i);
                        break;
                    }
                }
            }
        }
        return afs;
    }

}
