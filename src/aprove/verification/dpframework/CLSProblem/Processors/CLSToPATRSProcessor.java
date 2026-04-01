package aprove.verification.dpframework.CLSProblem.Processors;

import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Condition.*;
import aprove.verification.dpframework.CLSProblem.*;
import aprove.verification.dpframework.CLSProblem.Utility.*;
import aprove.verification.dpframework.PATRSProblem.*;
import aprove.verification.dpframework.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

@NoParams
public class CLSToPATRSProcessor extends CLSProcessor {

    private static Logger log =
        Logger.getLogger("aprove.verification.dpframework,CLSProblem.Processors.CLSToPATRSProcessor");

    private final static TRSTerm TERM_0 = PredefinedHelper.termInt("0");
    private final static TRSTerm TERM_1 = PredefinedHelper.termInt("1");

    private final static EnumSet<PredefinedFunctions>
        SUPPORTED_SYMBOLS = EnumSet.of(
                PredefinedFunctions.Not,
                PredefinedFunctions.And,
                PredefinedFunctions.Or,
                PredefinedFunctions.Add,
                PredefinedFunctions.Sub,
                PredefinedFunctions.Neg,
                PredefinedFunctions.Ceq,
                PredefinedFunctions.Cge,
                PredefinedFunctions.Cgt,
                PredefinedFunctions.Cle,
                PredefinedFunctions.Clt);

    @Override
    public boolean isCLSApplicable(CLSProblem obl) {
        EnumSet<PredefinedFunctions> unsupported =
            obl.getUsedPredefinedFunctions();
        unsupported.removeAll(CLSToPATRSProcessor.SUPPORTED_SYMBOLS);
        if (unsupported.isEmpty()) {
            return true;
        } else {
            CLSToPATRSProcessor.log.info("Problem contains unsupported predefined function symbols: " + unsupported);
            return false;
        }
    }

    private static final FunctionSymbol SYMBOL_AND =
        PredefinedFunctions.And.getSym();
    private static final FunctionSymbol SYMBOL_OR =
        PredefinedFunctions.Or.getSym();
    private static final FunctionSymbol SYMBOL_CEQ =
        PredefinedFunctions.Ceq.getSym();
    private static final FunctionSymbol SYMBOL_CGT =
        PredefinedFunctions.Cgt.getSym();
    private static final FunctionSymbol SYMBOL_CGE =
        PredefinedFunctions.Cge.getSym();

    private static final NameConflictResolver PATRS_NCR =
        NameConflictResolver.create(
                PredefinedHelper.getNameProvider(),
                PATRSPredefinedNames.getNameProvider());
    private static final TRSEval TRANSFORM_ARITH =
        new TRSEval(
                "(VAR x y)\n" +
                "(RULES\n" +
                "   Neg(x) -> -(x)\n" +
                "   Add(x, y) -> +(x, y)\n" +
                "   Sub(x, y) -> Add(x, -(y))\n" +
                ")");

    private static final List<FunctionSymbol> RHS_TRANSFORM_SYMS;
    static {
        RHS_TRANSFORM_SYMS = new ArrayList<FunctionSymbol>(
                PredefinedHelper.RELATION_SYMBOLS.size()+1);
        // Order is important. Not must be first! (so Not(Ceq(...))) is transformed
        // to the Rhs instead of Ceq(...) first and then Not(...) in removeRelationsFormRhs
        CLSToPATRSProcessor.RHS_TRANSFORM_SYMS.add(PredefinedFunctions.Not.getSym());
        CLSToPATRSProcessor.RHS_TRANSFORM_SYMS.addAll(PredefinedHelper.RELATION_SYMBOLS);
    }


    @Override
    protected Result processCLS(CLSProblem problem, Abortion aborter) throws AbortionException {
        // XXX: Assumptions And, ... nur auf booleschen Werten

        Set<ConditionalRule> rules = problem.getRules();

        /* Check that boolean operators occur only
         * in the condition, i.e. not in lhs or rhs.
         *
         * XXX: Move this check to isApplicable? Better yet, move it to problem creation?
         */
        Set<FunctionSymbol> lrsymbols = new HashSet<FunctionSymbol>();
        for(ConditionalRule rule : rules) {
            lrsymbols.addAll(rule.getLeft().getFunctionSymbols());
            lrsymbols.addAll(rule.getRight().getFunctionSymbols());
        }

        lrsymbols.retainAll(PredefinedHelper.CONDITION_SYMBOLS);
        if (!lrsymbols.isEmpty()) {
            // FIXME: do some error handling?
            assert(false);
        }

        /* Create PA rules */
        ImmutableSet<PARule> iPaRules =
            ImmutableCreator.create(this.transformRules(rules));

        /* We have no semantic data structures, so S and E just contain PA stuff */
        Set<Rule> s = this.getPAS();
        ImmutableSet<Rule> iS = ImmutableCreator.create(s);

        Set<Equation> e = this.getPAE();
        ImmutableSet<Equation> iE = ImmutableCreator.create(e);

        ImmutableMap<String, ImmutableList<String>> sortMap =
            this.getSorts(iPaRules);

        PATRSProblem patrs = PATRSProblem.create(iPaRules, iS, iE, sortMap);

        return ResultFactory.proved(patrs, YNMImplication.SOUND, new CLSToPATRSProof());
    }

    private Set<PARule> transformRules(Set<ConditionalRule> rules) {
        Queue<ConditionalRule> origQ =
             new LinkedList<ConditionalRule>();

        for (ConditionalRule rule : rules ) {
            rule = CLSToPATRSProcessor.PATRS_NCR.transformConditional(rule);

            // XXX: Document CLS assumption, that lhs is always a function application? (rhs too?)
            TRSFunctionApplication paL =
                (TRSFunctionApplication)CLSToPATRSProcessor.TRANSFORM_ARITH.normalize(rule.getLeft());
            TRSTerm paR = CLSToPATRSProcessor.TRANSFORM_ARITH.normalize(rule.getRight());

            paL = (TRSFunctionApplication)CondToDNF.CEQ2NOT_NORMALIZER.normalize(paL);
            paR = CondToDNF.CEQ2NOT_NORMALIZER.normalize(paR);

            ConditionalRule normalizedRule =
                ConditionalRule.create(paL, paR, rule.getConditions());

            origQ.add(normalizedRule);
        }

        List<ConditionalRule> normalized = this.removeRelationsFromRhs(origQ);
        return this.transformNormalizedCRuleToPAConstraint(normalized);
    }

    /**
     * Removes relation symbols from the rhs.
     *
     * <p>
     * This is done by moving the comparison to the condition
     * and replacing it by 0 or 1 at the original position
     * </p>
     * @param origQ Rules to work on. Is empty afterwards.
     */
    private List<ConditionalRule> removeRelationsFromRhs(
            Queue<ConditionalRule> origQ) {
        List<ConditionalRule>  transformed =
            new ArrayList<ConditionalRule>(origQ.size());
        outer : while(!origQ.isEmpty()) {
            ConditionalRule r = origQ.poll();
            if (Globals.useAssertions) {
                // Test for no relation symbols on the lhs.
                // XXX: Should this be guaranteed? How are the semantics of CLS?
                Set<FunctionSymbol> leftSyms = r.getLeft().getFunctionSymbols();
                leftSyms.retainAll(PredefinedHelper.RELATION_SYMBOLS);
                assert(leftSyms.isEmpty());
            }

            TRSFunctionApplication lhs = r.getLeft();
            TRSTerm rhs = r.getRight();

            for (FunctionSymbol that : CLSToPATRSProcessor.RHS_TRANSFORM_SYMS) {
                Position p = this.findSym(rhs, that);

                if (p == null) {
                    continue;
                }

                Condition newCond;
                ConditionalRule newRule;
                TRSTerm subterm = rhs.getSubterm(p);

                /* Create rule for condition evaluates to 1 */
                newCond = Condition.create(subterm, CLSToPATRSProcessor.TERM_1, ConditionType.ARROW);
                newRule = ConditionalRule.create(lhs, rhs.replaceAt(p, CLSToPATRSProcessor.TERM_1),
                        this.extendConds(r, newCond));
                origQ.add(newRule);

                /* Create rule for condition evaluates to 0 */
                subterm = TRSTerm.createFunctionApplication(
                        PredefinedFunctions.Not.getSym(),
                        new TRSTerm[] {subterm});
                newCond = Condition.create(subterm, CLSToPATRSProcessor.TERM_1, ConditionType.ARROW);
                newRule = ConditionalRule.create(lhs, rhs.replaceAt(p, CLSToPATRSProcessor.TERM_0),
                        this.extendConds(r, newCond));
                origQ.add(newRule);

                continue outer;
            }

            transformed.add(r);
        }
        return transformed;
    }

    /**
     * Finds the first position in Term t where FunctionSymbol fs
     * occurs.
     */
    private Position findSym(TRSTerm t, FunctionSymbol fs) {
        return this.findSym(t, fs, Position.create());
    }

    private Position findSym(TRSTerm t, FunctionSymbol fs, Position p) {
        if (t.isVariable()) {
            return null;
        }

        TRSFunctionApplication fa = (TRSFunctionApplication)t;

        if (fa.getRootSymbol().equals(fs)) {
            return p;
        }

        List<? extends TRSTerm> args = fa.getArguments();
        for (int i = 0; i < args.size(); i++) {
            Position pa = this.findSym(args.get(i), fs, p.append(i));
            if (pa != null) {
                return pa;
            }
        }

        return null;
    }

    private ImmutableList<Condition> extendConds(ConditionalRule rule, Condition c) {
        List<Condition> newConds =
            new ArrayList<Condition>(rule.getConditions());
        newConds.add(c);
        return ImmutableCreator.create(newConds);
    }

    /**
     * Transforms CLS rules to PAConstraints by transforming the constraints.
     *
     * LHS and RHS must be free of predefined CLS symbols; the only
     * transformation is done on the constraints.
     *
     * @param rules
     * @return
     */
    private Set<PARule> transformNormalizedCRuleToPAConstraint(
            List<ConditionalRule> rules) {
        Set<PARule> parules = new LinkedHashSet<PARule>();
        for (ConditionalRule rule : rules) {
            TRSFunctionApplication paL = rule.getLeft();
            TRSTerm paR = rule.getRight();

            List<Condition> conds = rule.getConditions();

            Set<ImmutableSet<PAConstraint>> dnfConstraints =
                this.transformConstraints(conds);

            for (ImmutableSet<PAConstraint> constraint : dnfConstraints) {
                PARule parule = PARule.create(paL, paR, constraint);
                parules.add(parule);
            }
            if (dnfConstraints.isEmpty()) {
                Set<PAConstraint> constraint = Collections.emptySet();
                PARule parule = PARule.create(paL, paR,
                        ImmutableCreator.create(constraint));
                parules.add(parule);
            }
        }
        return parules;
    }

    /**
     * Transform a list of CLS constraints to a set of sets of PAConstraints.
     *
     * <p>
     * PAConstraints allow no disjunction nor negation, so disjunction has
     * to be emulated by having multiple copies of a rule.
     * </p>
     */
    private Set<ImmutableSet<PAConstraint>> transformConstraints(
            List<Condition> conds) {
        TRSTerm bigCond = null;
        for (Condition cond : conds) {
            TRSTerm cL = cond.getLeft();
            TRSTerm cR = cond.getRight();
            ConditionType cT = cond.getType();

            /* For CLS problems, conditions are always of the form t -> 1, where t is a
             * boolean connection of atomic constraints. Atomic constraints are integer
             * relation of arithmetic expressions or arithmetic expressions.
             *
             * FIXME: Are arithmetic expressions actually possible?
             */
            if (!cR.equals(CLSToPATRSProcessor.TERM_1) || !cT.equals(ConditionType.ARROW)) {
                // FIXME: error handling.
                assert(false);
            }

            if (bigCond == null) {
                bigCond = cL;
            } else {
                bigCond = TRSTerm.createFunctionApplication(CLSToPATRSProcessor.SYMBOL_AND, bigCond, cL);
            }
        }

        if (bigCond == null) {
            return Collections.emptySet();
        }


        Set<TRSTerm> dnfTermConstraints =
            this.splitSym(CondToDNF.transform(bigCond), CLSToPATRSProcessor.SYMBOL_OR);
        Set <ImmutableSet<PAConstraint>> dnfConstraints =
            new HashSet<ImmutableSet<PAConstraint>>(dnfTermConstraints.size());
        for (TRSTerm andT : dnfTermConstraints) {
            Set<PAConstraint> pacs = new HashSet<PAConstraint>();
            for (TRSTerm atomicT : this.splitSym(andT, CLSToPATRSProcessor.SYMBOL_AND)) {
                pacs.add(this.makePAConstraint(atomicT));
            }

            dnfConstraints.add(ImmutableCreator.create(pacs));
        }
        return dnfConstraints;
    }

    /**
     * Transforms a term of the form "a sym b sym c" in
     * terms a, b, c
     */
    private Set<TRSTerm> splitSym(TRSTerm t, FunctionSymbol sym) {
        Set<TRSTerm> andSet = new HashSet<TRSTerm>();
        Queue<TRSTerm> todo = new LinkedList<TRSTerm>();
        todo.add(t);
        while(!todo.isEmpty()) {
            TRSTerm sub = todo.poll();
            if (this.hasRootSymbol(sub, sym)) {
                TRSFunctionApplication fa = (TRSFunctionApplication)sub;
                todo.add(fa.getArgument(0));
                todo.add(fa.getArgument(1));
            } else {
                andSet.add(sub);
            }
        }
        return andSet;
    }

    /**
     * Transforms an (atomic) constraint given as a Term to a PAConstraint.
     *
     * <p>The term constraint must be of the form REL(x, y), for REL in
     * Ceq, Clt, Cle, ..., 0, 1</p>
     *
     * FIXME sync with docu in transformRules
     */
    private PAConstraint makePAConstraint(TRSTerm t) {
        if (t.isVariable()) {
            throw new RuntimeException(
                    "Terms to be converted into a PAConstraint must have " +
                    "Ceq, Cgt or Cge as root function symbol: " + t);
        }

        TRSFunctionApplication fa = (TRSFunctionApplication)t;
        FunctionSymbol root = fa.getRootSymbol();

        // FIXME: Check args of CEQ, CGT.
        if (root.equals(CLSToPATRSProcessor.SYMBOL_CEQ)) {
            TRSTerm x = fa.getArgument(0);
            TRSTerm y = fa.getArgument(1);
            return PAConstraint.create(x, y, PAConstraint.EQ);
        } else if (root.equals(CLSToPATRSProcessor.SYMBOL_CGT)) {
            TRSTerm x = fa.getArgument(0);
            TRSTerm y = fa.getArgument(1);
            return PAConstraint.create(x, y, PAConstraint.GTR);
        } else if (root.equals(CLSToPATRSProcessor.SYMBOL_CGE)) {
            TRSTerm x = fa.getArgument(0);
            TRSTerm y = fa.getArgument(1);
            return PAConstraint.create(x, y, PAConstraint.GTREQ);
        } else {
            throw new RuntimeException(
                    "Terms to be converted into a PAConstraint must have " +
                    "Ceq, Cgt or Cge as root function symbol: " + t);
        }

    }

    /* CLS defined symbols always have a signature Int* -> Univ */
    private ImmutableMap<String, ImmutableList<String>>
            getSorts(Collection<PARule> rules) {
        Map<String, ImmutableList<String>> sortMap =
            new HashMap<String, ImmutableList<String>>(rules.size());

        // FIXME: Can we have different signatures for the same function symbol name?
        // and for the same function symbol? ~> Collision handling
        for (PARule rule : rules) {
            // lhs
            TRSFunctionApplication lhs = rule.getLeft();
            String name = lhs.getRootSymbol().getName();
            int argc = lhs.getArguments().size();

            List<String> sorts = new Vector<String>(Collections.nCopies(argc, "int"));
            sorts.add("univ");
            ImmutableList<String> sortEntry =
                ImmutableCreator.create(sorts);
            sortMap.put(name, sortEntry);

            // rhs
            TRSTerm rhs = rule.getRight();
            if (rhs instanceof TRSFunctionApplication) {
                TRSFunctionApplication rhss = (TRSFunctionApplication) rhs;
                name = rhss.getRootSymbol().getName();
                argc = rhss.getArguments().size();

                sorts = new Vector<String>(Collections.nCopies(argc, "int"));
                sorts.add("univ");
                sortEntry =
                    ImmutableCreator.create(sorts);
                sortMap.put(name, sortEntry);
            }
        }

        // add entries for +, -, 0, 1
        List<String> si = new Vector<String>();
        si.add("int");
        List<String> sii = new Vector<String>();
        sii.add("int");
        sii.add("int");
        List<String> siii = new Vector<String>();
        siii.add("int");
        siii.add("int");
        siii.add("int");
        sortMap.put("0", ImmutableCreator.create(si));
        sortMap.put("1", ImmutableCreator.create(si));
        sortMap.put("-", ImmutableCreator.create(sii));
        sortMap.put("+", ImmutableCreator.create(siii));

        return ImmutableCreator.create(sortMap);
    }

    private boolean hasRootSymbol(TRSTerm t, FunctionSymbol fs) {
        return !t.isVariable()
            && ((TRSFunctionApplication)t).getRootSymbol().equals(fs);
    }

    public class CLSToPATRSProof extends DefaultProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return "Converted to PATRS problem";
        }

    }

    // create E and S for PA symbols
    private Set<Equation> getPAE() {
        Set<Equation> res = new LinkedHashSet<Equation>();

        TRSVariable x = TRSTerm.createVariable("x");
        TRSVariable y = TRSTerm.createVariable("y");
        TRSVariable z = TRSTerm.createVariable("z");
        FunctionSymbol plus = FunctionSymbol.create("+", 2);

        res.add(this.constructA(plus, x, y, z));
        res.add(this.constructC(plus, x, y));

        return res;
    }

    private Set<Rule> getPAS() {
        Set<Rule> res = new LinkedHashSet<Rule>();

        TRSVariable x = TRSTerm.createVariable("x");
        TRSVariable y = TRSTerm.createVariable("y");
        FunctionSymbol zero = FunctionSymbol.create("0", 0);
        FunctionSymbol minus = FunctionSymbol.create("-", 1);
        FunctionSymbol plus = FunctionSymbol.create("+", 2);

        res.add(this.constructU(plus, zero, x, false));
        res.add(this.constructMM(minus, x));
        res.add(this.constructMZ(minus, zero));
        res.add(this.constructMP(minus, plus, x, y));
        res.addAll(this.constructCancel(plus, minus, zero, x, y));

        return res;
    }

    private Equation constructA(FunctionSymbol f, TRSVariable x, TRSVariable y, TRSVariable z) {
        Vector<TRSTerm> args = new Vector<TRSTerm>();
        args.add(y);
        args.add(z);
        TRSTerm fyz = this.createTerm(f, args);
        args = new Vector<TRSTerm>();
        args.add(x);
        args.add(fyz);
        TRSTerm fxfyz = this.createTerm(f, args);

        args = new Vector<TRSTerm>();
        args.add(x);
        args.add(y);
        TRSTerm fxy = this.createTerm(f, args);
        args = new Vector<TRSTerm>();
        args.add(fxy);
        args.add(z);
        TRSTerm ffxyz = this.createTerm(f, args);

        return Equation.create(fxfyz, ffxyz);
    }

    private Equation constructC(FunctionSymbol f, TRSVariable x, TRSVariable y) {
        Vector<TRSTerm> args = new Vector<TRSTerm>();
        args.add(x);
        args.add(y);
        TRSTerm fxy = this.createTerm(f, args);
        args = new Vector<TRSTerm>();
        args.add(y);
        args.add(x);
        TRSTerm fyx = this.createTerm(f, args);

        return Equation.create(fxy, fyx);
    }

    private Rule constructU(FunctionSymbol f, FunctionSymbol unit, TRSVariable x, boolean left) {
        Vector<TRSTerm> args = new Vector<TRSTerm>();
        if (left) {
            args.add(this.createTerm(unit, new Vector<TRSTerm>()));
            args.add(x);
        } else {
            args.add(x);
            args.add(this.createTerm(unit, new Vector<TRSTerm>()));
        }
        TRSFunctionApplication lhs = this.createTerm(f, args);

        return Rule.create(lhs, x);
    }

    private Rule constructMM(FunctionSymbol minus, TRSVariable x) {
        Vector<TRSTerm> args = new Vector<TRSTerm>();
        args.add(x);
        TRSFunctionApplication tmp = this.createTerm(minus, args);

        args = new Vector<TRSTerm>();
        args.add(tmp);
        TRSFunctionApplication lhs = this.createTerm(minus, args);
        return Rule.create(lhs, x);
    }

    private Rule constructMZ(FunctionSymbol minus, FunctionSymbol zero) {
        TRSFunctionApplication zerot = this.createTerm(zero, new Vector<TRSTerm>());
        Vector<TRSTerm> args = new Vector<TRSTerm>();
        args.add(zerot);
        TRSFunctionApplication lhs = this.createTerm(minus, args);
        return Rule.create(lhs, zerot);
    }

    private Rule constructMP(FunctionSymbol minus, FunctionSymbol plus, TRSVariable x, TRSVariable y) {
        Vector<TRSTerm> args = new Vector<TRSTerm>();
        args.add(x);
        args.add(y);
        TRSFunctionApplication fxy = this.createTerm(plus, args);

        args = new Vector<TRSTerm>();
        args.add(fxy);
        TRSFunctionApplication lhs = this.createTerm(minus, args);

        args = new Vector<TRSTerm>();
        args.add(x);
        TRSFunctionApplication gx = this.createTerm(minus, args);

        args = new Vector<TRSTerm>();
        args.add(y);
        TRSFunctionApplication gy = this.createTerm(minus, args);

        args = new Vector<TRSTerm>();
        args.add(gx);
        args.add(gy);
        TRSFunctionApplication rhs = this.createTerm(plus, args);

        return Rule.create(lhs, rhs);
    }

    private Set<Rule> constructCancel(FunctionSymbol plus, FunctionSymbol minus, FunctionSymbol zero, TRSVariable x, TRSVariable y) {
        Set<Rule> res = new LinkedHashSet<Rule>();
        TRSFunctionApplication zerot = this.createTerm(zero, new Vector<TRSTerm>());

        Vector<TRSTerm> args = new Vector<TRSTerm>();
        args.add(x);
        TRSFunctionApplication gx = this.createTerm(minus, args);

        args = new Vector<TRSTerm>();
        args.add(x);
        args.add(gx);
        TRSFunctionApplication lhs = this.createTerm(plus, args);
        res.add(Rule.create(lhs, zerot));

        args = new Vector<TRSTerm>();
        args.add(lhs);
        args.add(y);
        lhs = this.createTerm(plus, args);
        res.add(Rule.create(lhs, y));

        return res;
    }

    private TRSFunctionApplication createTerm(FunctionSymbol f, List<TRSTerm> args) {
        TRSTerm[] nargs = new TRSTerm[args.size()];
        for (int i = 0; i < args.size(); i++) {
            nargs[i] = args.get(i);
        }
        return TRSTerm.createFunctionApplication(f, nargs);
    }
}
