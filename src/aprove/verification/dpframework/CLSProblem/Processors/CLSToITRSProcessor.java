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
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.dpframework.Utility.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

@NoParams
public class CLSToITRSProcessor extends CLSProcessor {

    private static Logger log =
        Logger.getLogger("aprove.verification.dpframework,CLSProblem.Processors.CLSToITRSProcessor");

    /**
     * Domain which is used for the ITRS integers: Z
     */
    private final static IntegerDomain DOMAIN = DomainFactory.INTEGERS;

    /**
     * Converts CLS integers to ITRS integers
     */
    private final static TermVisitor INT_CONVERTER =
        new ITRSIntTermVisitor();

    private final static TRSTerm CLS_TERM_1 = PredefinedHelper.termInt("1");

    private final static TRSTerm ITRS_TERM_0 = PredefinedSemanticsFactory.getInt(BigIntImmutable.ZERO, CLSToITRSProcessor.DOMAIN).getTerm();
    private final static TRSTerm ITRS_TERM_1 = PredefinedSemanticsFactory.getInt(BigIntImmutable.ONE, CLSToITRSProcessor.DOMAIN).getTerm();


    private final static EnumSet<PredefinedFunctions>
        SUPPORTED_SYMBOLS = EnumSet.of(
                PredefinedFunctions.Not,
                PredefinedFunctions.And,
                PredefinedFunctions.Or,

                PredefinedFunctions.Add,
                PredefinedFunctions.Sub,
                PredefinedFunctions.Mul,
                PredefinedFunctions.Div,
                PredefinedFunctions.Neg,

                PredefinedFunctions.Ceq,
                PredefinedFunctions.Cge,
                PredefinedFunctions.Cgt,
                PredefinedFunctions.Cle,
                PredefinedFunctions.Clt);

    private static final FunctionSymbol ITRS_AND = IDPPredefinedMap.DEFAULT_MAP.getSym(Func.Land, DomainFactory.BOOLEAN_BOOLEAN);

    private static final NameConflictResolver ITRS_NCR =
        NameConflictResolver.create(
                PredefinedHelper.getNameProvider(),
                IDPPredefinedMap.DEFAULT_MAP);

    private static final List<FunctionSymbol> RHS_TRANSFORM_SYMS;
    static {
        RHS_TRANSFORM_SYMS = new ArrayList<FunctionSymbol>(
                PredefinedHelper.RELATION_SYMBOLS.size()+1);
        // Order is important. Not must be first! (so Not(Ceq(...))) is transformed
        // to the Rhs instead of Ceq(...) first and then Not(...) in removeRelationsFormRhs
        CLSToITRSProcessor.RHS_TRANSFORM_SYMS.add(PredefinedFunctions.Not.getSym());
        CLSToITRSProcessor.RHS_TRANSFORM_SYMS.addAll(PredefinedHelper.RELATION_SYMBOLS);
    }

    @Override
    public boolean isCLSApplicable(CLSProblem obl) {
        /* Check that no unsupported predefined symbols occur */
        EnumSet<PredefinedFunctions> unsupported =
            obl.getUsedPredefinedFunctions();
        unsupported.removeAll(CLSToITRSProcessor.SUPPORTED_SYMBOLS);
        if (!unsupported.isEmpty()) {
            CLSToITRSProcessor.log.info("Problem contains unsupported predefined function symbols: " + unsupported);
            return false;
        }

        /* Check that no predefined symbols occur on the lhs. */
        // FIXME: Can we move this check to problem creation?
        // FIXME: This does not check for integers!
        Set<FunctionSymbol> lsymbols = new HashSet<FunctionSymbol>();
        for(ConditionalRule rule : obl.getRules()) {
            lsymbols.addAll(rule.getLeft().getFunctionSymbols());
        }

        lsymbols.retainAll(PredefinedHelper.PREDEF_SYMS);
        if (!lsymbols.isEmpty()) {
            CLSToITRSProcessor.log.info("Problem contains predefined function symbols on lhs of a rule: " + lsymbols);
            return false;
        }

        return true;
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
        Set<FunctionSymbol> rsymbols = new HashSet<FunctionSymbol>();
        for(ConditionalRule rule : rules) {
            rsymbols.addAll(rule.getRight().getFunctionSymbols());
        }

        rsymbols.retainAll(PredefinedHelper.CONDITION_SYMBOLS);
        if (!rsymbols.isEmpty()) {
            // FIXME: do some error handling?
            assert(false);
        }

        /* Create integer rules */
        Set<GeneralizedRule> newRules = IGeneralizedRule.removeConditions(this.transformRules(rules));
        ImmutableSet<GeneralizedRule> iNewRules = ImmutableCreator.create(newRules);

        QTermSet qts = new QTermSet(CollectionUtils.getLeftHandSides(newRules));
        IQTermSet iqts = new IQTermSet(qts, IDPPredefinedMap.DEFAULT_MAP);
        ITRSProblem itrs = ITRSProblem.create(iNewRules, iqts);

        return ResultFactory.proved(itrs, YNMImplication.SOUND, new CLSToITRSProof());
    }

    /**
     * Transforms arithmetic symbols to CLS. This does not modify the conditions.
     *
     * FIXME: We assume that conditions do not contain arithmetic symbols (except
     * for integer constants). Is that correct?
     */
    private Set<IGeneralizedRule> transformRules(Set<ConditionalRule> rules) {
        Queue<ConditionalRule> origQ =
             new LinkedList<ConditionalRule>();

        for (ConditionalRule rule : rules ) {
            rule = CLSToITRSProcessor.ITRS_NCR.transformConditional(rule);

            // XXX: Document CLS assumption, that lhs is always a function application? (rhs too?)
            TRSTerm iR = CondToDNF.CEQ2NOT_NORMALIZER.normalize(rule.getRight());

            ConditionalRule normalizedRule =
                ConditionalRule.create(rule.getLeft(), iR, rule.getConditions());

            origQ.add(normalizedRule);
        }

        List<ConditionalRule> normalized = this.removeRelationsFromRhs(origQ);
        return this.transformNormalizedCRuleToIRule(normalized);
    }

    /**
     * Removes relation symbols from the rhs.
     *
     * <p>
     * This is done by moving the comparison to the condition and replacing it
     * by 0 or 1 at the original position
     * </p>
     *
     * <p>
     * This pass must be done before converting the relation symbols with
     * INT_CONVERTER, as it relies on the CLS function symbols.
     * </p>
     *
     * @param origQ
     *            Rules to work on. Is empty afterwards.
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

            for (FunctionSymbol that : CLSToITRSProcessor.RHS_TRANSFORM_SYMS) {
                Position p = this.findSym(rhs, that);

                if (p == null) {
                    continue;
                }

                Condition newCond;
                ConditionalRule newRule;
                TRSTerm subterm = rhs.getSubterm(p);

                /* Create rule for condition evaluates to 1 */
                newCond = Condition.create(subterm, CLSToITRSProcessor.CLS_TERM_1, ConditionType.ARROW);
                newRule = ConditionalRule.create(lhs, rhs.replaceAt(p, CLSToITRSProcessor.ITRS_TERM_1),
                        this.extendConds(r, newCond));
                origQ.add(newRule);

                /* Create rule for condition evaluates to 0 */
                subterm = TRSTerm.createFunctionApplication(
                        PredefinedFunctions.Not.getSym(),
                        new TRSTerm[] {subterm});
                newCond = Condition.create(subterm, CLSToITRSProcessor.CLS_TERM_1, ConditionType.ARROW);
                newRule = ConditionalRule.create(lhs, rhs.replaceAt(p, CLSToITRSProcessor.ITRS_TERM_0),
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
     * Transforms CLS rules to IRules by transforming the constraints.
     *
     * LHS and RHS must be free of predefined CLS symbols; the only
     * transformation is done on the constraints.
     */
    private Set<IGeneralizedRule> transformNormalizedCRuleToIRule(
            List<ConditionalRule> rules) {
        Set<IGeneralizedRule> irules = new LinkedHashSet<IGeneralizedRule>();
        for (ConditionalRule rule : rules) {
            TRSFunctionApplication paL = rule.getLeft();
            TRSTerm paR = CLSToITRSProcessor.INT_CONVERTER.start(rule.getRight());

            List<Condition> conds = rule.getConditions();

            TRSTerm c = this.transformConstraints(conds);

            irules.add(IGeneralizedRule.create(paL, paR, c));
        }
        return irules;
    }

    /**
     * Transform a list of CLS constraints to a constraint for IRules.
     *
     * XXX: We assume, that each CLS constraint is typesafe with the intuitive
     * boolean, integer types for relations and boolean operators. We probably
     * should check (or statically ensure) this.
     */
    private TRSTerm transformConstraints(
            List<Condition> conds) {
        TRSTerm bigCond = null;
        for (Condition cond : conds) {
            TRSTerm cL = CondToDNF.CEQ2NOT_NORMALIZER.normalize(cond.getLeft());
            TRSTerm cR = cond.getRight();
            ConditionType cT = cond.getType();

            /* For CLS problems, conditions are always of the form t -> 1, where t is a
             * boolean connection of atomic constraints. Atomic constraints are integer
             * relation of arithmetic expressions or arithmetic expressions.
             *
             * FIXME: Are arithmetic expressions actually possible?
             */
            if (!cR.equals(CLSToITRSProcessor.CLS_TERM_1) || !cT.equals(ConditionType.ARROW)) {
                // FIXME: error handling.
                assert(false);
            }

            if (cL.equals(cR)) {
                continue;
            }

            cL = CLSToITRSProcessor.INT_CONVERTER.start(cL);

            if (bigCond == null) {
                bigCond = cL;
            } else {
                bigCond = TRSTerm.createFunctionApplication(
                        CLSToITRSProcessor.ITRS_AND, bigCond, cL);
            }
        }

        return bigCond;
    }

    public class CLSToITRSProof extends DefaultProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return "Converted to ITRS problem";
        }

    }

}
