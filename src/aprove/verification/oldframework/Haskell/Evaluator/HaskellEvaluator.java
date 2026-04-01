package aprove.verification.oldframework.Haskell.Evaluator;

import java.util.*;

import aprove.*;
import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Patterns.*;
import aprove.verification.oldframework.Haskell.Substitutors.*;
import aprove.verification.oldframework.Haskell.Typing.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * @author Stephan Swiderski
 *
 * HaskellEvaluator evaluates an HaskellTerm at his next redex
 * (real haskell strategie)
 */
public class HaskellEvaluator {
    public static final HaskellObject joker = new Var(new HaskellNamedSym("", "_"));

    /**
     * Determines whether arguments of strict constructors are considered
     * right-to-left, as is required by the Haskell98 report (in case this is <code>true</code>),
     * or whether the behavior as implemented in Hugs and GHC is used, i.e.,
     * strict arguments are traversed from left-to-right (in case this is <code>false</code>).
     */
    public static final boolean STANDARD_COMPLIANT_STRICT_CONSTRUCTOR_ORDER = false;

    Set<VarEntity> varEntities;
    RuleBlockMap ruleBlockMap;
    HaskellObject lastRedex;
    public Prelude prelude;
    private HaskellEntity errorEntity;
    public HaskellEntity errorFrameEntity;
    public HaskellEntity termiEntity;
    public Pair<RuleBlock, HaskellSubstitution> termiPair;

    private Pair<RuleBlock, HaskellSubstitution> insufficientArgumentsPair;

    protected int currentSubtermID = 0;

    public Map<TyClassEntity, List<InstEntity>> classInstMap = new HashMap<TyClassEntity, List<InstEntity>>();

    private VarEntity getEntity(final String name) {
        return (VarEntity) this.prelude.getEntity(this.prelude, "Prelude", name, HaskellEntity.Sort.VAR);
    }

    public void initEntities(final Set<HaskellEntity> entities) {
        this.currentSubtermID = 0;
        this.errorEntity = this.getEntity("error");
        this.errorFrameEntity = this.getEntity("errorFrame");
        this.termiEntity = this.getEntity("terminator");
        this.termiPair = new Pair<RuleBlock, HaskellSubstitution>(null, null);
        this.insufficientArgumentsPair = new Pair<RuleBlock, HaskellSubstitution>(null, null);
        this.varEntities = new HashSet<VarEntity>();
        this.ruleBlockMap =
            new RuleBlockMap(this.errorEntity, this.termiEntity, this.termiPair, this.insufficientArgumentsPair);
        final Set<TyClassEntity> tcles = new LinkedHashSet<TyClassEntity>();
        for (final HaskellEntity e : entities) {
            if (e instanceof CVarEntity) {

            } else if (e instanceof VarEntity) {
                this.varEntities.add((VarEntity) e);
                if ((e.getSort() == HaskellEntity.Sort.VAR)) {
                    this.ruleBlockMap.addRuleBlock(e, new RuleBlock(((Function) e.getValue())));
                }
            }
            if (e instanceof InstEntity) {
                final InstEntity ie = (InstEntity) e;
                final Set<HaskellEntity> ines = ie.getSubEntities();
                final TyClassEntity tcle = (TyClassEntity) ie.getTyClassEntity();
                tcles.add(tcle);
                List<InstEntity> ies = this.classInstMap.get(tcle);
                if (ies == null) {
                    ies = new Vector<InstEntity>();
                    this.classInstMap.put(tcle, ies);
                }
                ies.add(ie);
                final Set<HaskellEntity> cles = new HashSet<HaskellEntity>(tcle.getSubEntities());
                for (final HaskellEntity ine : ines) {
                    final InstFunction ifunc = ((InstFunction) ine.getValue());
                    final VarEntity ve = (VarEntity) ifunc.getSymbol().getEntity();
                    final Function func = ifunc.getFunction();
                    this.ruleBlockMap.addRuleBlock(ve, new RuleBlock(func));
                    cles.remove(ve);
                }
                final HaskellType instanceType = ((TypeSchema) ie.getType()).getMatrix();
                for (final HaskellEntity cle : cles) {
                    final Function func = ((Function) cle.getValue());
                    final MemberTypeSchema mts = (MemberTypeSchema) cle.getType();
                    final ClassConstraint cc = mts.getClassConstraint();
                    final HaskellSubstitution preSubs = new HaskellSubstitution((Var) cc.getType(), instanceType);
                    if (func != null) {
                        this.ruleBlockMap.addRuleBlock(cle,
                            new RuleBlock(func, (HaskellType) preSubs.applyTo(mts.getMatrix()), preSubs));
                    } else {
                        this.ruleBlockMap.addRuleBlock(cle, new RuleBlock(new Vector<HaskellRule>(),
                            (HaskellType) preSubs.applyTo(mts.getMatrix()), 0, preSubs));
                    }
                }
            }
        }
        for (final TyClassEntity tcle : tcles) {
            for (final HaskellEntity cle : tcle.getSubEntities()) {
                final MemberTypeSchema mts = (MemberTypeSchema) cle.getType();
                final ClassConstraint cc = mts.getClassConstraint();
                this.ruleBlockMap.addRuleBlock(cle, new RuleBlock((Var) cc.getType(), mts.getMatrix()));
            }
        }
    }

    public HaskellObject addSubtermIDs(HaskellObject exp) {
        final HaskellSubstitution subs = new HaskellSubstitution();
        exp = subs.applyToWithSubtermNumbering((BasicTerm) exp, this.currentSubtermID);
        this.currentSubtermID = subs.getNewSubtermIDMax();
        return exp;
    }

    public Result evaluate(final HaskellObject exp) {

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.println(">>>>>>input Term:"+exp);
        }

        // TODO verify whether Copy.deep is needed
        final Result res = this.match(true, false, null, Copy.deep(exp), null);

        if (res instanceof TermResult) {
            final TermResult tRes = (TermResult) res;
            final HaskellObject term = tRes.getTerm();
            final HaskellObject nexp = Copy.deep(exp);
            this.typeChecker(term);
            this.typeChecker(nexp);
            tRes.setTerm(nexp.visit(new SubtermReplacer(term, tRes.getSubtermID())));
            this.typeChecker(tRes.getTerm());
        }

        return res;
    }

    public HaskellObject getLastRedex() {
        return this.lastRedex;
    }

    public boolean isWHNO(final HaskellObject exp) {
        final List<HaskellObject> exps = HaskellTools.applyFlatten(exp);
        final HaskellObject ehead = exps.get(0);
        return (ehead instanceof Cons);
    }

    public boolean hasCorrectArity(final HaskellObject exp) {
        final List<HaskellObject> exps = HaskellTools.applyFlatten(exp);
        final Atom ehead = (Atom) exps.remove(0);
        if (ehead.getBasicSort() == BasicTerm.Sort.VAR) {
            final VarEntity ve = (VarEntity) ehead.getSymbol().getEntity();
            if (!ve.getLocal()) {
                return this.ruleBlockMap.hasCorrectArity(exps.size(), ve, ehead.getTypeTerm());
            }
        }
        return true;
    }

    public Result forceEval(final HaskellObject exp,
        final Iterator<HaskellObject> eit,
        final int arity,
        final HaskellSubstitution subs) {
        int position = 0;
        while (eit.hasNext()) {
            position++;
            final Result res = this.match(false, false, null, eit.next(), subs);
            if (!res.matched())
             {
                return res; //this.setPosition(exp,res,arity,position);
            }
        }
        return new MatchResult(true);
    }

    /**
     * Determines whether a given constructor has at least one
     * strict argument.
     * @param ce The constructor entity to check.
     * @return True if there is at least one strict argument,
     * false otherwise.
     */
    private boolean isStrictCons(final ConsEntity ce) {
        for (final boolean b : ce.getStrictness()) {
            if (b) {
                return true;
            }
        }
        return false;
    }

    /**
     * Matches the arguments of a strict constructor against those of a pattern.
     * This is done by first trying to match all strict arguments, then the non-strict
     * ones. Thereby, the evaluation of strict arguments is done first, before trying to
     * match non-strict ones. This corresponds to the semantics that a strict constructor
     * is interpreted as (\x1 ... xn -> C op_1 x1 op_2 ... op_n xn) where op_i = $! if the
     * i-th position is strict and op_i = $ otherwise.
     * The direction of traversing the arguments is however depending on the value of
     * {@link #STANDARD_COMPLIANT_STRICT_CONSTRUCTOR_ORDER}, to either implement the
     * behavior of Hugs and GHC (left-to-right also for strict arguments), or the behavior
     * when the above lambda functions specified in the Haskell98 report are used, which
     * results in a right-to-left traversal of strict arguments.
     * @param termCe The strict constructor of the term to be matched. This is
     * used to determine the strictness flags.
     * @param patternIt An iterator that returns the pattern arguments. This iterator should
     * return as next element the first pattern.
     * @param exprIt An iterator that returns the arguments of the term constructor termCe,
     * which are to be matched by the pattern. This iterator should return as next element
     * the first argument of the term constructor.
     * @param subs A substitution in which the matching will be stored if successful.
     * @return A true MatchResult if the matching succeeded for all arguments, a false one
     * if it did not, and TermResult, (Ty)CaseResult, ErrorResult, etc. if there was a position
     * where the matching requires further evaluation.
     */
    private Result matchStrictConstructor(final ConsEntity termCe,
        final ListIterator<HaskellObject> patternIt,
        final ListIterator<HaskellObject> exprIt,
        final HaskellSubstitution subs) {
        ListIterator<Boolean> strictnessIt;
        if (HaskellEvaluator.STANDARD_COMPLIANT_STRICT_CONSTRUCTOR_ORDER) {
            final List<Boolean> strictnessFlags = termCe.getStrictness();
            strictnessIt = strictnessFlags.listIterator(strictnessFlags.size());

            // advance the iterators to the end
            while (exprIt.hasNext()) {
                patternIt.next();
                exprIt.next();
            }
        } else {
            strictnessIt = termCe.getStrictness().listIterator();
        }

        // handle strict arguments first and store the non-strict ones for later
        final List<Pair<HaskellObject, HaskellObject>> nonStrictPatAndExprs =
            new ArrayList<Pair<HaskellObject, HaskellObject>>(termCe.getArity());
        for (boolean advance = (HaskellEvaluator.STANDARD_COMPLIANT_STRICT_CONSTRUCTOR_ORDER) ? exprIt.hasPrevious() : exprIt.hasNext(); advance; advance =
            (HaskellEvaluator.STANDARD_COMPLIANT_STRICT_CONSTRUCTOR_ORDER) ? exprIt.hasPrevious() : exprIt.hasNext()) {
            boolean strictArg;
            HaskellObject patternArg;
            HaskellObject exprArg;
            if (HaskellEvaluator.STANDARD_COMPLIANT_STRICT_CONSTRUCTOR_ORDER) {
                strictArg = strictnessIt.previous();
                patternArg = patternIt.previous();
                exprArg = exprIt.previous();
            } else {
                strictArg = strictnessIt.next();
                patternArg = patternIt.next();
                exprArg = exprIt.next();
            }
            if (strictArg) {
                final Result res = this.match(false, strictArg, patternArg, exprArg, subs);
                if (!res.matched()) {
                    // continue if we get an insufficient arguments error,
                    // in this case we have a WHNF of functional type
                    if (!(res instanceof InsufficientArgumentsResult)) {
                        return res;
                    }
                }
            } else {
                // non strict arg, so store for later
                nonStrictPatAndExprs.add(new Pair<HaskellObject, HaskellObject>(patternArg, exprArg));
            }
        }

        if (HaskellEvaluator.STANDARD_COMPLIANT_STRICT_CONSTRUCTOR_ORDER) {
            // these have to always be handled left-to-right
            Collections.reverse(nonStrictPatAndExprs);
        }

        // handle the non-strict arguments next
        for (final Pair<HaskellObject, HaskellObject> nonStrictPatAndExpr : nonStrictPatAndExprs) {
            final Result res = this.match(false, false, nonStrictPatAndExpr.x, nonStrictPatAndExpr.y, subs);
            if (!res.matched()) {
                return res;
            }
        }
        return new MatchResult(true);
    }

    protected Result match(final boolean top,
        final boolean strict,
        final HaskellObject pat,
        final HaskellObject exp,
        final HaskellSubstitution subs) {
        boolean normal = true;
        this.lastRedex = exp;

        final List<HaskellObject> exps = HaskellTools.applyFlatten(exp);
        final int arity = exps.size();
        final ListIterator<HaskellObject> eit = exps.listIterator();
        final Atom ehead = (Atom) eit.next();
        if (pat instanceof Var) {
            if (pat != HaskellEvaluator.joker) {
                subs.put(((Var) pat).getSymbol(), exp);
            }

            if (!strict) {
                return new MatchResult(true);
            }
            // strictness must be handled
            normal = false;
        }
        if (ehead.getBasicSort() == BasicTerm.Sort.CONS) {
            if (pat == null) {
                return this.forceEval(exp, eit, arity, subs);
            } else {
                ListIterator<HaskellObject> pit = null;
                final ConsEntity termCe = (ConsEntity) ehead.getSymbol().getEntity();
                final boolean termCeIsStrict = this.isStrictCons(termCe);
                boolean matchResult = true;
                if (normal) {
                    pit = HaskellTools.applyFlatten(pat).listIterator();

                    // pat is not a variable (because normal is true), so it must start with a constructor
                    final ConsEntity patCe = (ConsEntity) ((Atom) pit.next()).getSymbol().getEntity();
                    if (patCe != termCe) {
                        if (!termCeIsStrict) {
                            return new MatchResult(false);
                        }

                        // the term constructor is strict, so we need to descend into it
                        matchResult = false;
                        normal = false;
                    }
                }
                // this is not else to the above if-block, since normal can be changed there
                if (!normal) {
                    // pat is var or not matching, but strictness forces evaluation of strict parameters
                    // of the current constructor in exp
                    pit = Collections.nCopies(termCe.getArity(), HaskellEvaluator.joker).listIterator();
                }

                if (termCeIsStrict) {
                    // handle strict constructor, which has different order of traversing arguments
                    final Result res = this.matchStrictConstructor(termCe, pit, eit, subs);
                    if (res instanceof MatchResult) {
                        // add whether the constructor itself matched into the result
                        return new MatchResult(matchResult && res.matched());
                    }
                    return res;
                }

                // the term constructor is not strict, so it must still be matching
                if (Globals.useAssertions) {
                    assert (matchResult);
                }
                while (eit.hasNext()) {
                    final HaskellObject patternArg = pit.next();
                    final HaskellObject exprArg = eit.next();
                    final Result res = this.match(false, false, patternArg, exprArg, subs);
                    if (!res.matched()) {
                        return res;
                    }
                }
                return new MatchResult(true);
            }
        } else {
            final VarEntity ve = (VarEntity) ehead.getSymbol().getEntity();
            if (ve.getLocal()) {
                if (pat == null || (!normal)) {
                    return this.forceEval(exp, eit, arity, subs);
                } else {
                    if (exps.size() > 1) {
                        return this.getReplacement(top, exp, exps, ve);
                    }
                    return new CaseResult((Var) ehead);

                }
            } else {
                return this.getReplacement(top, exp, exps, ve);
            }
        }
    }

    public Result newTermiVar(final HaskellObject exp) {
        return new ErrorResult(ErrorType.Other, null, 0);
    }

    public Result getReplacement(final boolean top,
        final HaskellObject exp,
        final List<HaskellObject> exps,
        final VarEntity ve) {
        final HaskellObject ehead = exps.get(0);
        final int arity = exps.size();
        final Result crres = this.checkRedex(top, ehead, exp, exps);
        if (crres != null) {
            return crres;
        }
        final Pair<RuleBlock, HaskellSubstitution> rbs =
            this.ruleBlockMap.getRuleBlock(exps.size() - 1, ve, ehead.getTypeTerm());
        if (rbs == this.termiPair) {
            return this.newTermiVar(ehead);
        }
        if (rbs == this.insufficientArgumentsPair) {
            return new InsufficientArgumentsResult(ErrorType.Other, null, 2);
        }
        if (rbs == null) {

            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                //System.out.println("ty1 No rule for:  "+exp);
                //System.out.println("ty1 No rule for:  "+exp.getTypeTerm());
            }

            return new ErrorResult(ErrorType.ErrorCall, exps.get(1), 3);
        }
        if (rbs.getKey().getRules() == null) {
            final Var var = rbs.getKey().getTypeVariable();
            final HaskellSubstitution subs = rbs.getValue();
            final BasicTerm rep = subs.applyTo(var);
            return new TyCaseResult(ve, ehead.getTypeTerm(), (HaskellType) rep, ((BasicTerm) exp).getSubtermNumber());
        }
        Outer: for (HaskellRule rule : rbs.getKey().getRules()) {
            HaskellSubstitution subs = new HaskellSubstitution();
            final Iterator<HaskellPat> pit = rule.getPatterns().iterator();
            final Iterator<HaskellObject> eit = exps.iterator();
            eit.next();
            int position = 0;

            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                //System.out.println("$$$$ match $rule test: "+exp);
            }

            final Result cres = this.checkRule(top, rbs, ve, ehead, arity, rule, exp);
            if (cres != null) {
                return cres;
            }
            while (pit.hasNext()) {
                position++;
                final Result res = this.match(false, false, pit.next(), eit.next(), subs);
                if (ve == this.errorFrameEntity) {
                    if (res.isError()) {
                        final ErrorResult eres = (ErrorResult) res;
                        rule = rbs.getKey().getRules().get(eres.getErrorFrameNumber());
                        final Var varX = (Var) ((Apply) rule.getPatterns().get(0)).getArgument();
                        if (eres.getErrStr() == null) {
                            subs = new HaskellSubstitution();
                        } else {
                            subs = new HaskellSubstitution(varX, (BasicTerm) eres.getErrStr());
                        }
                        return this.applicateRule(top, rbs, ve, ehead, arity, rule, subs, exp);
                    }
                }
                if (res.interrupt()) {
                    return res;
                }
                if (!res.matched()) {
                    continue Outer;
                }
            }
            return this.applicateRule(top, rbs, ve, ehead, arity, rule, subs, exp);

        }
        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.println("No rule for:  "+exp);
            //System.out.println("No rule for:  "+exp.getTypeTerm());

            /*        System.out.println("###->"+exp);
                System.out.println("###:>"+ve);
                System.out.println("###:>"+exp.getTypeTerm());

                Iterator<Apply> it = new SubTermIterator(exp);
                while (it.hasNext()){
                    Apply apply = it.next();
                    HaskellExp sterm = (HaskellExp) apply.getArgument();
                    System.out.println("   "+sterm+" :: "+sterm.getTypeTerm());
                }
             */
        }
        return new ErrorResult(ErrorType.PatternMatchFailure, null, 2);
    }

    public Result checkRedex(final boolean top,
        final HaskellObject ehead,
        final HaskellObject redex,
        final List<HaskellObject> exps) {
        return null;
    }

    public Result checkRule(final boolean top,
        final Pair<RuleBlock, HaskellSubstitution> rbs,
        final VarEntity ve,
        final HaskellObject ehead,
        final int arity,
        final HaskellRule rule,
        final HaskellObject redex) {
        return null;
    }

    public Result applicateRule(final boolean top,
        final Pair<RuleBlock, HaskellSubstitution> rbs,
        final VarEntity ve,
        final HaskellObject ehead,
        final int arity,
        final HaskellRule rule,
        final HaskellSubstitution subs,
        final HaskellObject redex) {
        return this.setRhsInExp(rbs, subs, redex, arity, rule.getExpression(), rule);
    }

    public Result setRhsInExp(final Pair<RuleBlock, HaskellSubstitution> rbs,
        final HaskellSubstitution subs,
        HaskellObject redex,
        final int arity,
        HaskellObject nexp,
        final HaskellRule rule) {
        final HaskellObject oexp = Copy.deep(nexp);
        final HaskellObject ored = Copy.deep(redex);
        nexp = subs.applyToWithSubtermNumbering((BasicTerm) nexp, this.currentSubtermID);
        this.currentSubtermID = subs.getNewSubtermIDMax();
        final int i = arity - rbs.getKey().getArity() - 2;
        (new TypeAnnotationSubstitutor(rbs.getValue())).applyTo(nexp);
        if (this.typeChecker(nexp)) {
            final Vector<Object> vec = new Vector<Object>();
            vec.add(rbs);
            vec.add(subs);
            vec.add(redex);
            vec.add(ored);
            vec.add(oexp);
            vec.add(rule);
            HaskellSym.showee(vec);
            throw new RuntimeException();
        }

        /*arity = 6
        count = 5


        (0 1) 2) 3) 4) 5 (position)

            - 4  3  2  1  0 (app dec count)
         */

        if (i >= 0) {
            final Apply apply = HaskellTools.applyGet((Apply) redex, i);
            //apply.setFunction(nexp);
            redex = apply.getFunction();
        } else {
            //redex = nexp;
        }

        return new TermResult(nexp, ((BasicTerm) redex).getSubtermNumber());
    }

    public boolean typeChecker(final HaskellObject ho) {
        if (ho instanceof Apply) {
            final Apply app = (Apply) ho;
            final BasicTerm fu = this.prelude.buildArrow(app.getArgument().getTypeTerm(), app.getTypeTerm());
            if (!(fu.equivalentTo(app.getFunction().getTypeTerm()))) {

                System.err.println("ERROR: Wrong types found.");

                // XXX DEBUG
                if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                    //System.out.println(app);
                    //System.out.println(fu);
                    //System.out.println((BasicTerm)app.getFunction().getTypeTerm());
                }

                return true;
            }
            ;
            return this.typeChecker(app.getFunction()) || this.typeChecker(app.getArgument());
        }
        return false;

    }

}
