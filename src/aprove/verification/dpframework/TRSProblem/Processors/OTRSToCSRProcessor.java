package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Utility.FreshVarGenerator;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.dpframework.TRSProblem.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * "From Outermost to Context-Sensitive Rewriting" <br>
 * Joerg Endrullis and Dimitri Hendriks <br>
 * Bib: [ENDRULLIS_HENDRIKS_2009] <br>
 * @author Tim Enger
 */

public class OTRSToCSRProcessor extends OTRSProcessor {

    /**
     * there are two versions available<br>
     * minimal and maximal labeling
     */
    private final boolean minimalLabeling;

    /**
     * otrs to transform
     */
    private OTRSProblem otrs;

    /**
     * \Sigma^{top} = \Sigma \cup {fresh symbol: top}
     */
    private Set<FunctionSymbol> sigmaTop;

    /**
     * all redex symbols
     */
    private Set<FunctionSymbol> sigmaRed;

    /**
     * the contructed minimized core RedexAlgebra
     */
    private MinimizedRedexAlgebra algebra;

    /**
     * extension symbol for \Sigma^Top
     */
    private FunctionSymbol top;

    /**
     * labelsymbol for minimal labeling
     */
    private String star = "^*";

    FreshNameGenerator gen;
    /**
     * maps labels to integer to improve readability<br>
     * a label is a List of equivalence classes of the MinimizedRedexAlgebra
     */
    private LinkedHashMap<List<Set<TRSFunctionApplication>>, Integer> labelMapping;
    private int count = 0;

    @Override
    public boolean isOTRSApplicable(final OTRSProblem otrs) {
        if (Options.certifier.isCeta()) {
            return false;
        }
        /**
         * if the otrs has rules that are not proper we can't handle this
         * because the CSRProblem can't handle GeneralizedRules<br>
         * in general the transformation could handle those otrs.<br>
         * only dynamic labeling needs to be adjusted
         */
        for (final GeneralizedRule rule : otrs.getR()) {
            if (!rule.getLeft().getVariables().containsAll(
                rule.getRight().getVariables())) {
                return false;
            }
        }
        return true;
    }

    @ParamsViaArgumentObject
    public OTRSToCSRProcessor(final Arguments args) {
        this.minimalLabeling = args.minimalLabeling;
    }

    @Override
    protected Result processOTRS(final OTRSProblem otrs,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException {

        this.otrs = otrs;
        final Set<FunctionSymbol> signature =
            new LinkedHashSet<FunctionSymbol>(otrs.getSignature());

        this.labelMapping =
            new LinkedHashMap<List<Set<TRSFunctionApplication>>, Integer>();

        this.gen =
            new FreshNameGenerator(signature, FreshNameGenerator.APPEND_NUMBERS);

        /*** create top and star ***/
        this.top = FunctionSymbol.create(this.gen.getFreshName("*top*", false), 1);
        this.star = this.gen.getFreshName("^*", false);

        // Lemma: 3.8 add a fresh constant and a fresh unary Symbol
        final FunctionSymbol constant =
            FunctionSymbol.create(this.gen.getFreshName("c", false), 0);
        final FunctionSymbol unSym =
            FunctionSymbol.create(this.gen.getFreshName("s", false), 1);

        signature.add(constant);
        signature.add(unSym);

        aborter.checkAbortion();

        /*** construct a suitable Algebra ***/
        this.algebra = new MinimizedRedexAlgebra(otrs.getR(), signature);
        this.algebra.extendTop(this.top);

        aborter.checkAbortion();

        /*** build \Sigma_Top ***/
        this.sigmaTop = new LinkedHashSet<FunctionSymbol>(signature);
        this.sigmaTop.add(this.top);

        /*** build \Sigma_Red ***/
        this.sigmaRed = new LinkedHashSet<FunctionSymbol>();
        for (final FunctionSymbol f : this.sigmaTop) {
            if (this.minimalLabeling) {
                // \Sigma^{red} = {f^star | f \in \Sigma}
                final String freshName = this.gen.getFreshName(f.getName() + this.star, true);
                this.sigmaRed.add(FunctionSymbol.create(freshName, f.getArity()));
            } else { // maximal labeling
                // if f is a constant don't label it
                if (f.getArity() == 0) {
                    // but add it, if it is a redex
                    if (this.algebra.isRedex(f,
                        new ArrayList<Set<TRSFunctionApplication>>())) {
                        this.sigmaRed.add(f);
                    }
                } else {
                    // \Sigma^{red} = {f^{a_1,...,a_n} | isRedex_f(a_1,...,a_n) = true}
                    for (final List<Set<TRSFunctionApplication>> args : Combinations.createCombinations(
                        new ArrayList<Set<TRSFunctionApplication>>(this.algebra.getE()),
                        f.getArity())) {
                        if (this.algebra.isRedex(f, args)) {
                            final Integer label = this.labelMapping.get(args);
                            if (label != null) {
                                final String freshName =
                                    this.gen.getFreshName(f.getName() + "^" + label,
                                        true);
                                this.sigmaRed.add(FunctionSymbol.create(freshName,
                                    f.getArity()));
                            } else {
                                final String freshName =
                                    this.gen.getFreshName(f.getName() + "^" + this.count,
                                        true);
                                final FunctionSymbol newF =
                                    FunctionSymbol.create(freshName,
                                        f.getArity());
                                this.sigmaRed.add(newF);
                                this.labelMapping.put(args, this.count++);
                            }
                        }
                    }
                }
            }
        }

        aborter.checkAbortion();

        if (Globals.DEBUG_NEX) {
            System.err.println("sigmaTop: " + this.sigmaTop + "\n");
            System.err.println("sigmaRed: " + this.sigmaRed + "\n");
        }

        /*** dynamic context extension ***/
        Set<Pair<GeneralizedRule, Function>> setP =
            new LinkedHashSet<Pair<GeneralizedRule, Function>>();

        // compute P_0
        for (final GeneralizedRule rule : otrs.getR()) {
            final List<TRSVariable> vars =
                new ArrayList<TRSVariable>(rule.getLeft().getVariables());

            for (final List<Set<TRSFunctionApplication>> comb : Combinations.createCombinations(
                new ArrayList<Set<TRSFunctionApplication>>(this.algebra.getE()),
                vars.size())) {
                final Function fun = new Function();
                for (int i = 0; i < vars.size(); i++) {
                    fun.addMapping(vars.get(i), comb.get(i));
                }
                setP.add(new Pair<GeneralizedRule, Function>(rule, fun));
            }
        }

        setP = this.computeDynamicContextExt(setP);

        if (Globals.DEBUG_NEX) {
            System.err.println("dynamic context extension:");
            for (final Pair<GeneralizedRule, Function> p : setP) {
                System.err.println(p);
            }
        }

        aborter.checkAbortion();

        /*** dynamic labeling ***/
        // we use Rules from now on !!!
        final Set<Rule> dynLab = new LinkedHashSet<Rule>();
        for (final Pair<GeneralizedRule, Function> pair : setP) {
            final TRSFunctionApplication lhs = pair.x.getLeft();
            final TRSTerm rhs = pair.x.getRight();
            dynLab.add(Rule.create((TRSFunctionApplication) this.lab(lhs, pair.y), this.lab(
                rhs, pair.y)));
        }

        // build replacementMap
        final Map<FunctionSymbol, Set<Integer>> replacementMap =
            new LinkedHashMap<FunctionSymbol, Set<Integer>>();

        final Set<FunctionSymbol> labSigma = CollectionUtils.getFunctionSymbols(dynLab);

        for (final FunctionSymbol f : this.sigmaRed) {
            if (labSigma.contains(f)) {
                replacementMap.put(f, new LinkedHashSet<Integer>());
            }
        }

        labSigma.removeAll(this.sigmaRed);

        for (final FunctionSymbol f : labSigma) {
            final Set<Integer> pos = new LinkedHashSet<Integer>();
            for (int i = 0; i < f.getArity(); i++) {
                pos.add(i);
            }
            replacementMap.put(f, pos);
        }

        if (Globals.DEBUG_NEX) {
            System.err.println("\nmapping:" + this.labelMapping);
        }

        /*** finished ***/
        final CSRProblem csr = CSRProblem.create(dynLab, replacementMap, false);

        if (this.minimalLabeling) {
            return ResultFactory.proved(csr, YNMImplication.SOUND,
                new OTRSToCSRProof());
        } else {
            if (otrs.isQuasiLeftLinear()) {
                return ResultFactory.proved(csr, YNMImplication.EQUIVALENT,
                    new OTRSToCSRProof());
            } else {
                return ResultFactory.proved(csr, YNMImplication.SOUND,
                    new OTRSToCSRProof());
            }
        }
    }

    /**
     * [x,alpha] = alpha(x) with Variable x <br>
     * [f(t_1,...,t_n),alpha] = [f]([t_1,alpha],...,[t_n,alpha])<br>
     * where [.] is the interpretation function of the redex-Algebra
     * @param t {@link TRSTerm} to evaluate
     * @param alpha {@link Function} for {@link TRSVariable} mapping
     * @return the interpretet Term
     */
    public Set<TRSFunctionApplication> interpret(final TRSTerm t, final Function alpha) {
        if (t.isVariable()) {
            return alpha.eval((TRSVariable) t);
        } else {
            final TRSFunctionApplication funApp = (TRSFunctionApplication) t;
            final ArrayList<Set<TRSFunctionApplication>> args =
                new ArrayList<Set<TRSFunctionApplication>>();
            for (final TRSTerm arg : funApp.getArguments()) {
                args.add(this.interpret(arg, alpha));
            }
            return this.algebra.interpret(funApp.getRootSymbol(), args);
        }
    }

    /**
     * dynamic context extension
     * @param p0
     * @return
     */
    @SuppressWarnings("unchecked")
    private Set<Pair<GeneralizedRule, Function>> computeDynamicContextExt(final Set<Pair<GeneralizedRule, Function>> p0) {

        final Set<NonEmptyContext> cbl = this.computeCbl();

        Set<Pair<GeneralizedRule, Function>> setP = p0;

        // to store all pairs that are equal
        // because those don't need to be checked in futher iterations
        final Set<Pair<GeneralizedRule, Function>> equalPairs =
            new LinkedHashSet<Pair<GeneralizedRule, Function>>();

        // iterate until P_i = P_{i+1}
        boolean changed = true;
        while (changed) {
            changed = false;

            final Set<Pair<GeneralizedRule, Function>> newP =
                new LinkedHashSet<Pair<GeneralizedRule, Function>>();

            for (final Pair<GeneralizedRule, Function> pair : setP) {
                final Set<TRSFunctionApplication> interL =
                    this.interpret(pair.x.getLeft(), pair.y);
                final Set<TRSFunctionApplication> interR =
                    this.interpret(pair.x.getRight(), pair.y);
                final Function alpha = pair.y;

                if (!interL.equals(interR) || pair.x.getRight().isVariable()) {
                    changed = true;

                    // we have to replace this rule
                    // compute \Delta(l -> r, alpha)
                    final Set<Pair<GeneralizedRule, Function>> delta =
                        new LinkedHashSet<Pair<GeneralizedRule, Function>>();

                    for (NonEmptyContext c : cbl) {
                        // create alpha + beta
                        final List<TRSVariable> varsC =
                            new ArrayList<TRSVariable>(
                                (Set<TRSVariable>)CollectionUtils.getVariables(c.getTermsAfterDirectSubcontext())
                            );
                        varsC.addAll((Set<TRSVariable>)CollectionUtils.getVariables(c.getTermsBeforeDirectSubcontext()));
                        for (List<Set<TRSFunctionApplication>> comb : Combinations.createCombinations(
                            new ArrayList<Set<TRSFunctionApplication>>(
                                this.algebra.getE()), varsC.size())) {
                            final Function alphabeta = new Function(alpha);
                            for (int i = 0; i < varsC.size(); i++) {
                                alphabeta.addMapping(varsC.get(i), comb.get(i));
                            }

                            // root(lab(C[l], alpha+beta)) \notin \SigmaRed
                            final TRSFunctionApplication lhs = pair.x.getLeft();
                            final TRSTerm labeled =
                                this.lab(c.replace(lhs),
                                    alphabeta);

                            if (!this.sigmaRed.contains(((TRSFunctionApplication) labeled).getRootSymbol())) {
                                final GeneralizedRule newRule =
                                    GeneralizedRule.create(
                                        (TRSFunctionApplication) c.replace(lhs),
                                        c.replace(pair.x.getRight()));
                                delta.add(new Pair<GeneralizedRule, Function>(
                                    newRule, alphabeta));
                            }
                        }
                    }
                    newP.addAll(delta);
                } else {
                    equalPairs.add(pair);
                }
            }
            setP = newP;
        }
        return equalPairs;
    }

    /**
     * flat contexts fresh C^b_t
     * @param sig
     * @return flat context fresh
     */
    private Set<NonEmptyContext> computeCbl() {
        final Set<NonEmptyContext> context = new LinkedHashSet<NonEmptyContext>();
        for (final FunctionSymbol f : this.sigmaTop) {
            for (int j = 1; j <= f.getArity(); j++) {
                final ArrayList<TRSTerm> args = new ArrayList<TRSTerm>();
                @SuppressWarnings("unchecked")
                final Set<TRSVariable> usedVars = (Set<TRSVariable>)CollectionUtils.getVariables(this.otrs.getR());
                final FreshVarGenerator varGen = new FreshVarGenerator(usedVars);
                // create fresh vars x_1,...,x_{j-1}
                for (int i = 1; i <= j - 1; i++) {
                    args.add(varGen.getFreshVariable(
                        TRSTerm.createVariable("x"), false));
                }
                // position for context
                final int[] pos = { j - 1 };
                args.add(varGen.getFreshVariable(TRSTerm.createVariable("x"), true));
                // create fresh vars x_{j+1},...,x_{fArity}
                for (int i = j + 1; i <= f.getArity(); i++) {
                    args.add(varGen.getFreshVariable(
                        TRSTerm.createVariable("x"), false));
                }
                final TRSFunctionApplication funApp =
                    TRSTerm.createFunctionApplication(f, ImmutableCreator.create(args));
                final NonEmptyContext con = (NonEmptyContext) Context.create(funApp, Position.create(pos));
                context.add(con);
            }
        }
        return context;
    }

    /**
     * for Variables x: lab(x,a)=x <br>
     * lab(f(t_1,...,t_n),a) =
     * f^{\pi_f([t_1,a],...,[t_n,a])}(lab(t_1,a),...,lab(t_n,a)) <br>
     * @param t {@link TRSTerm} to label
     * @return labeled Term
     */
    private TRSTerm lab(final TRSTerm t, final Function alpha) {
        if (t.isVariable()) {
            return t;
        } else {
            final TRSFunctionApplication funApp = (TRSFunctionApplication) t;
            final ArrayList<TRSTerm> args = new ArrayList<TRSTerm>();
            final ArrayList<Set<TRSFunctionApplication>> argsLab = new ArrayList<Set<TRSFunctionApplication>>();
            for (final TRSTerm arg : funApp.getArguments()) {
                args.add(this.lab(arg, alpha));
                argsLab.add(this.interpret(arg, alpha));
            }
            final FunctionSymbol labSym = this.getLabel(funApp.getRootSymbol(), argsLab, alpha);
            return TRSTerm.createFunctionApplication(labSym, ImmutableCreator.create(args));
        }
    }

    /**
     * \pi_f - label function
     * @param f
     * @param args
     * @param alpha
     * @return the labeled {@link FunctionSymbol}, note that not every
     * {@link FunctionSymbol} gets labeled
     */
    private FunctionSymbol getLabel(final FunctionSymbol f,
        final List<Set<TRSFunctionApplication>> args,
        final Function alpha) {

        if (this.minimalLabeling) {
            if (this.algebra.isRedex(f, args)) {
                final String freshName = this.gen.getFreshName(f.getName() + this.star, true);
                final FunctionSymbol newSym =
                    FunctionSymbol.create(freshName, f.getArity());
                return newSym;
            } else {
                return f;
            }
        } else { // maximal
            // we don't label constants
            if (f.getArity() == 0) {
                return f;
            }

            final Integer label = this.labelMapping.get(args);
            if (label != null) {
                final String freshName =
                    this.gen.getFreshName(f.getName() + "^" + label, true);
                return FunctionSymbol.create(freshName, f.getArity());
            } else {
                final String freshName =
                    this.gen.getFreshName(f.getName() + "^" + this.count, true);
                final FunctionSymbol newF =
                    FunctionSymbol.create(freshName, f.getArity());
                this.labelMapping.put(args, this.count++);
                return newF;
            }
        }
    }

    /**
     * class to represent {@link TRSVariable} -> {@link TRSFunctionApplication}
     * mappings
     * @author Tim Enger
     */
    private class Function {

        private final Map<TRSVariable, Set<TRSFunctionApplication>> mapping;

        public Function() {
            this.mapping = new LinkedHashMap<TRSVariable, Set<TRSFunctionApplication>>();
        }

        public Function(final Function f) {
            this.mapping =
                new LinkedHashMap<TRSVariable, Set<TRSFunctionApplication>>(f.mapping);
        }

        public void addMapping(final TRSVariable var, final Set<TRSFunctionApplication> f) {
            this.mapping.put(var, f);
        }

        public Set<TRSFunctionApplication> eval(final TRSVariable t) {
            return this.mapping.get(t);
        }

        @Override
        public String toString() {
            return String.valueOf(this.mapping);
        }

        @Override
        public int hashCode() {
            final int result = ((this.mapping == null) ? 0 : this.mapping.hashCode());
            return result;
        }

        @Override
        public boolean equals(final Object obj) {
            if (this == obj) {
                return true;
            }
            if (obj == null) {
                return false;
            }
            if (this.getClass() != obj.getClass()) {
                return false;
            }
            final Function other = (Function) obj;
            if (this.mapping == null) {
                if (other.mapping != null) {
                    return false;
                }
            } else if (!this.mapping.equals(other.mapping)) {
                return false;
            }
            return true;
        }
    }

    private static class OTRSToCSRProof extends QTRSProof {

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "Transformation from Outermost to Context Sensitive according to "
                + o.cite(new Citation[] { Citation.ENDRULLIS_HENDRIKS_2009 })
                + '.';
        }
    }

    public static class Arguments {
        public boolean minimalLabeling = false;
    }

}
