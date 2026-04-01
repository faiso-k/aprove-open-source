package aprove.verification.dpframework.DPProblem.Processors;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.dpframework.TRSProblem.Processors.*;
import aprove.verification.dpframework.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * QDPUncurrying Processor<br>
 * "Uncurrying for Termination"<br>
 * Nao Hirokawa, Aart Middeldorp, Harald Zankl
 * @author Tim Enger
 */

public class QDPUncurryingProcessor extends QDPProblemProcessor {

    private final UncurryMethod method;

    private final boolean top;

    @ParamsViaArgumentObject
    public QDPUncurryingProcessor(final Arguments arguments) {
        this.method = arguments.method;
        this.top = arguments.top;
    }

    @Override
    public boolean isQDPApplicable(final QDPProblem qdp) {
        return QDPUncurryingProcessor.isUncurryingApplicable(qdp, this.method, this.top).x;
    }

    public static Pair<Boolean, FunctionSymbol> isUncurryingApplicable(final QDPProblem qdp,
        final UncurryMethod method,
        final boolean top) {
        // applicative
        final Pair<Boolean, FunctionSymbol> applicable = QDPUncurryingProcessor.getApplicativeInfo(qdp, method, top);
        final FunctionSymbol appSymbol = applicable.y;
        if (!applicable.x) {
            return new Pair<>(false, appSymbol);
        }
        // minimal
        if (!qdp.getMinimal()) {
            return new Pair<>(false, appSymbol);
        }
        // Q must be empty
        if (!qdp.getQ().isEmpty()) {
            return new Pair<>(false, appSymbol);
        }
        // the generalized method directly checks' if the app Symbol is left
        // head variable free otherwise this has to be done seperately
        if (!(method == UncurryMethod.GENERALIZED)) {
            final Set<Rule> rules = new LinkedHashSet<>(qdp.getR());
            rules.addAll(qdp.getP());
            if (!QDPUncurryingProcessor.getLeftHeadVarFree(rules, appSymbol)) {
                return new Pair<>(false, appSymbol);
            }
        }
        return new Pair<>(true, appSymbol);
    }

    /**
     * get applicative Info
     *
     * @param qdp
     *            QDPProblem
     * @return true, if the QDPProblem is applicative
     */
    private static Pair<Boolean, FunctionSymbol> getApplicativeInfo(final QDPProblem qdp,
        final UncurryMethod method,
        final boolean top) {
        final Pair<Boolean, FunctionSymbol> applicative;
        switch (method) {
        case HIRO_MIDDEL_ZANKL:
            if (Globals.useAssertions) {
                assert (top == false);
            }
            applicative = QDPUncurryingProcessor.getApplicativeInfoHMZ(qdp);
            break;
        case GENERALIZED:
            if (top) {
                applicative = QDPUncurryingProcessor.getApplicativeInfoGeneralizedP(qdp);
            } else {
                // TODO: this seems very strange, since it does not consider the pairs of the qdp!!
                applicative = QDPUncurryingProcessor.getApplicativeInfoGeneralizedR(qdp);
            }
            break;
        default:
            applicative = new Pair<Boolean, FunctionSymbol>(false, null);
            break;
        }
        return applicative;
    }

    private static Pair<Boolean, FunctionSymbol> getApplicativeInfoGeneralizedR(final QDPProblem qdp) {
        return QDPUncurryingProcessor.getApplicativeInfoGeneralizedR(qdp.getR());
    }

    public static Pair<Boolean, FunctionSymbol> getApplicativeInfoGeneralizedR(final Set<Rule> R) {
        final Map<FunctionSymbol, Integer> maybeApplicableSymbols = new LinkedHashMap<FunctionSymbol, Integer>();
        final Set<FunctionSymbol> notApplicative = new LinkedHashSet<FunctionSymbol>();
        final Set<TRSTerm> allTermsOfR = new LinkedHashSet<TRSTerm>();
        // Gather all terms
        for (final Rule rule : R) {
            allTermsOfR.add(rule.getLeft());
        }
        // Gather all function symbols that have arity 2
        for (final TRSTerm term : allTermsOfR) {
            for (final Map.Entry<FunctionSymbol, Integer> entry : term.getFunctionSymbolCount().entrySet()) {
                final FunctionSymbol fSym = entry.getKey();
                // check if symbol has arity 2 and is left head variable free
                // and remove if not
                if (fSym.getArity() == 2 && QDPUncurryingProcessor.symbolIsLeftHeadVarFree(fSym, term) && !notApplicative.contains(fSym)) {
                    final Integer occurences = entry.getValue();
                    QDPUncurryingProcessor.putAppSymbol(maybeApplicableSymbols, fSym, occurences);
                } else {
                    maybeApplicableSymbols.remove(fSym);
                    notApplicative.add(fSym);
                }
            }
        }
        FunctionSymbol appDummy = null;
        Integer min = 0;
        for (final Map.Entry<FunctionSymbol, Integer> entry : maybeApplicableSymbols.entrySet()) {
            final FunctionSymbol fSym = entry.getKey();
            final Integer i = entry.getValue();
            if (i > min && QDPUncurryingProcessor.getLeftHeadVarFree(R, fSym)) {
                appDummy = fSym;
                min = i;
            }
        }
        if (appDummy != null) {
            return new Pair<>(true, appDummy);
        }
        return new Pair<>(false, null);
    }

    private static Pair<Boolean, FunctionSymbol> getApplicativeInfoGeneralizedP(final QDPProblem qdp) {
        final Map<FunctionSymbol, Integer> maybeApplicableSymbols = new LinkedHashMap<FunctionSymbol, Integer>();
        final Set<FunctionSymbol> notApplicative = new LinkedHashSet<FunctionSymbol>();
        final Set<TRSTerm> allTermsOfP = new LinkedHashSet<TRSTerm>();
        // Gather all terms
        final Set<FunctionSymbol> heads = new LinkedHashSet<FunctionSymbol>(qdp.getHeadSymbols());
        for (final Rule rule : qdp.getP()) {
            allTermsOfP.add(rule.getLeft());
        }
        // Count how often the sharp Symbols occur
        for (final TRSTerm term : allTermsOfP) {
            if (term instanceof TRSFunctionApplication) {
                final TRSFunctionApplication funApp = (TRSFunctionApplication) term;
                final FunctionSymbol rootSym = funApp.getRootSymbol();
                if (funApp.isConstant() || funApp.getArgument(0).isVariable() || notApplicative.contains(rootSym)) {
                    heads.remove(rootSym);
                    notApplicative.add(rootSym);
                } else {
                    final Integer occurences = term.getFunctionSymbolCount().get(rootSym);
                    QDPUncurryingProcessor.putAppSymbol(maybeApplicableSymbols, rootSym, occurences);
                }
            }
        }
        FunctionSymbol appDummy = null;
        Integer min = 0;
        for (final Map.Entry<FunctionSymbol, Integer> entry : maybeApplicableSymbols.entrySet()) {
            final FunctionSymbol fSym = entry.getKey();
            final Integer i = entry.getValue();
            if (i > min && QDPUncurryingProcessor.getLeftHeadVarFree(qdp.getR(), fSym)) {
                appDummy = fSym;
                min = i;
            }
        }
        if (appDummy != null) {
            final Pair<Boolean, FunctionSymbol> appInfo = new Pair<Boolean, FunctionSymbol>(true, appDummy);
            return appInfo;
        }
        final Pair<Boolean, FunctionSymbol> appInfo = new Pair<Boolean, FunctionSymbol>(false, null);
        return appInfo;
    }

    private static void putAppSymbol(final Map<FunctionSymbol, Integer> counts,
        final FunctionSymbol fSym,
        final Integer occurences) {
        final Integer value = counts.get(fSym);
        if (value == null) {
            counts.put(fSym, occurences);
        } else {
            counts.put(fSym, value + occurences);
        }
    }

    private static Pair<Boolean, FunctionSymbol> getApplicativeInfoHMZ(final QDPProblem qdp) {
        FunctionSymbol appSymbol = null;
        // symbols in Q, R, and in P below root
        final Set<FunctionSymbol> P_Q_R = new LinkedHashSet<>(qdp.getRwithQ().getSignature());
        // symbols in P at root
        final Set<FunctionSymbol> P_root = new LinkedHashSet<>();
        for (final Rule rule : qdp.getP()) {
            P_Q_R.addAll(rule.getLeft().getNonRootFunctionSymbols());
            P_root.add(rule.getLeft().getRootSymbol());
            final TRSTerm rhs = rule.getRight();
            if (rhs.isVariable()) { // HMZ demands standard DP-Problem where rhss of P are no variables
                return new Pair<>(false, null);
            } else {
                final TRSFunctionApplication frhs = (TRSFunctionApplication) rhs;
                P_Q_R.addAll(frhs.getNonRootFunctionSymbols());
                P_root.add(frhs.getRootSymbol());
            }
        }
        // P_below R Q, there should be exactly 1 FctSymbol with arity 2
        for (final FunctionSymbol funsym : P_Q_R) {
            if (funsym.getArity() == 2) {
                if (appSymbol == null) {
                    appSymbol = funsym;
                } else if (!funsym.equals(appSymbol)) {
                    return new Pair<>(false, null);
                }
            } else if (funsym.getArity() != 0) {
                return new Pair<>(false, null);
            }
        }
        if (appSymbol == null) {
            return new Pair<>(false, null);
        }

        // P, all rootsymbols should have arity 2 or 0
        // and only 1 additonal FctSym with arity 2
        FunctionSymbol first = null;
        for (final FunctionSymbol funsym : P_root) {
            if (funsym.getArity() == 2) {
                if (first == null) {
                    first = funsym;
                } else if (!funsym.equals(first)) {
                    return new Pair<>(false, null);
                }
            } else if (funsym.getArity() != 0) {
                return new Pair<>(false, null);
            }
        }
        return new Pair<>(true, appSymbol);
    }

    private static boolean symbolIsLeftHeadVarFree(final FunctionSymbol fSym, final TRSTerm term) {
        final Triple<TRSTerm, FunctionSymbol[], TRSTerm[]> part = QDPUncurryingProcessor.partition(term, fSym, false);
        if (part.x.isVariable()) {
            return false;
        }
        return true;
    }

    private static boolean getLeftHeadVarFree(final Set<Rule> rules, final FunctionSymbol appSymbol) {

        for (final Rule rule : rules) {
            final Set<TRSTerm> terms = rule.getLeft().getSubTerms();
            terms.removeAll(rule.getLeft().getVariables());
            for (final TRSTerm term : terms) {
                final Triple<TRSTerm, FunctionSymbol[], TRSTerm[]> part = QDPUncurryingProcessor.partition(term, appSymbol, false);
                if (part.x.isVariable()) {
                    return false;
                }
            }
        }
        return true;
    }

    @Override
    protected Result processQDPProblem(final QDPProblem qdp, final Abortion aborter) throws AbortionException {
        // store export information
        final Set<Pair<FunctionSymbol, Set<FunctionSymbol>>> informationSet =
            new LinkedHashSet<>();

        final Map<FunctionSymbol, Integer> aa = new LinkedHashMap<>();
        final Set<Rule> u = new LinkedHashSet<>();
        Set<Rule> rEta = new LinkedHashSet<>();
        final Set<Rule> pEta = new LinkedHashSet<>();
        Set<Rule> p = new LinkedHashSet<>();
        final Set<Rule> rplus = new LinkedHashSet<>();
        final FunctionSymbol appSymbol;
        final FreshNameGenerator fg = new FreshNameGenerator(qdp.getSignature(), FreshNameGenerator.APPEND_NUMBERS);

        // compute the "applicative Symbol"
        appSymbol = QDPUncurryingProcessor.getApplicativeInfo(qdp, this.method, this.top).y;

        // applicative arities
        for (final FunctionSymbol fSym : qdp.getSignature()) {
            aa.put(fSym, 0);
        }
        aa.remove(appSymbol);
        if (this.top) {
            QDPUncurryingProcessor.computeApplicativeArities(qdp.getP(), aa, appSymbol);
        } else {
            QDPUncurryingProcessor.computeApplicativeArities(qdp.getR(), aa, false, appSymbol, this.method);
            QDPUncurryingProcessor.computeApplicativeArities(qdp.getP(), aa, true, appSymbol, this.method);
        }

        QDPUncurryingProcessor.computeU(u, aa, appSymbol, fg, informationSet);
        final ImmutableSet<Rule> uImmutable = ImmutableCreator.create(u);

        // rEta = R and eta-saturation
        rEta.addAll(qdp.getR());
        final Set<Rule> newEtaRules = new LinkedHashSet<Rule>();
        QDPUncurryingProcessor.computeREta(rEta, aa, appSymbol, newEtaRules, this.method);

        // pEta = P and eta-saturation if top currying
        pEta.addAll(qdp.getP());
        if (this.top) {
            QDPUncurryingProcessor.computeREta(pEta, aa, appSymbol, newEtaRules, this.method);
            rEta.removeAll(newEtaRules);
        }

        // normalize rEta w.r.t U
        rEta = QDPUncurryingProcessor.evalRules(uImmutable, rEta);
        // normalize P w.r.t. U
        p = QDPUncurryingProcessor.evalRules(uImmutable, pEta);
        // R+ = eEta u U
        rplus.addAll(rEta);

        if (!this.top) {
            rplus.addAll(uImmutable);
        } else {
            p.addAll(uImmutable);
        }

        // nothing happened?
        if ((!this.top && qdp.getR().equals(rplus) && qdp.getP().equals(p))
            || (this.top && qdp.getP().equals(p) && qdp.getR().equals(rplus))) {
            return ResultFactory.unsuccessful();
        }

        final QTRSProblem qtrs = QTRSProblem.create(ImmutableCreator.create(rplus));

        final QDPProblem newQDP = QDPProblem.create(p, qtrs, true);

        final Proof proof =
            new QDPUncurryingProof(newQDP, appSymbol, informationSet, uImmutable, newEtaRules, this.method,
                this.top);

        return ResultFactory.proved(newQDP, YNMImplication.EQUIVALENT, proof);
    }

    /**
     * eta-saturation of R
     * @param r Rules
     * @param aa applicative arities
     */
    public static void computeREta(final Set<Rule> R,
        final Map<FunctionSymbol, Integer> aa,
        final FunctionSymbol appDummy,
        final Set<Rule> newEtaRules,
        final UncurryMethod method) {
        final List<Rule> temp = new ArrayList<Rule>();
        final List<Rule> newR = new ArrayList<Rule>();
        int etaSize = 0;
        do {
            etaSize = newEtaRules.size();
            for (final Rule rule : R) {
                final int aaterm = QDPUncurryingProcessor.getAATerm(rule.getLeft(), aa, appDummy, method);
                if (aaterm > 0) {
                    final FreshNameGenerator fg =
                        new FreshNameGenerator(rule.getVariables(), FreshNameGenerator.APPEND_NUMBERS);

                    final ArrayList<TRSTerm> argsl = new ArrayList<TRSTerm>();
                    final ArrayList<TRSTerm> argsr = new ArrayList<TRSTerm>();

                    argsl.add(rule.getLeft());
                    argsr.add(rule.getRight());
                    for (int k = 1; k < appDummy.getArity(); k++) {
                        final String name = fg.getFreshName("x", false);
                        final TRSVariable new_x = TRSTerm.createVariable(name);

                        argsl.add(new_x);
                        argsr.add(new_x);
                    }

                    final TRSFunctionApplication fa_l =
                        TRSTerm.createFunctionApplication(appDummy, ImmutableCreator.create(argsl));

                    final TRSFunctionApplication fa_r =
                        TRSTerm.createFunctionApplication(appDummy, ImmutableCreator.create(argsr));

                    final Rule newRule = Rule.create(fa_l, fa_r);
                    temp.add(newRule);

                }
            }
            newR.addAll(R);
            R.clear();
            R.addAll(temp);
            newEtaRules.addAll(temp);
        } while (etaSize != newEtaRules.size());
        newR.addAll(newEtaRules);
        R.clear();
        R.addAll(newR);
    }

    /**
     * @param rules - non-null
     * @param rulestoeval - non-null, will not be modified
     * @return normalized rulestoeval w.r.t rules
     */
    public static Set<Rule> evalRules(final ImmutableSet<Rule> rules, final Set<Rule> rulestoeval) {
        final TRSEval evaluate = new TRSEval(rules);
        final Set<Rule> newRules = new LinkedHashSet<Rule>();

        for (final Rule rule : rulestoeval) {
            final TRSTerm left = evaluate.normalize(rule.getLeft());
            final TRSTerm right = evaluate.normalize(rule.getRight());
            newRules.add(Rule.create((TRSFunctionApplication) left, right));
        }

        return newRules;
    }

    /**
     * computes the set U Def. 9
     * @param u the set
     * @param aa the applicative arity of every function symbol
     * @param fg FreshNameGenerator
     * @param informationSet non-null; this method will add information
     *   obtained when computing U that will be needed for proof export
     */
    public static void computeU(final Set<Rule> u,
        final Map<FunctionSymbol, Integer> aa,
        final FunctionSymbol appDummy,
        final FreshNameGenerator fg,
        final Set<Pair<FunctionSymbol, Set<FunctionSymbol>>> informationSet) {

        for (final FunctionSymbol fct : aa.keySet()) {
            ArrayList<TRSVariable> argsf = new ArrayList<>();
            String name = null;

            /*
             * This part is only used for the xml export of this processor
             */
            final Set<FunctionSymbol> newSymbols = new LinkedHashSet<>();

            /*
             * f_i(x_1, ..., x_i)' y -> f_i+1 (x_1,....,x_i,y)
             *
             * i=0: app(f,x) -> f_1(x) i=1; app(f_1(x), x_1) -> f_2(x, x_1) i=2:
             * app(f_2(x, x_1), x_2) -> f_3(x, x_1, x_2)
             */
            final int fctAa;
            final Integer fctAaInt = aa.get(fct);
            if (fctAaInt != null) {
                fctAa = fctAaInt;
            } else {
                fctAa = 0;
            }
            int fctA;
            fctA = fct.getArity();
            newSymbols.add(fct);
            for (int i = fctA; i < (fctA + fctAa); i++) {
                argsf = new ArrayList<>(argsf.size());

                final ArrayList<TRSTerm> argsl = new ArrayList<TRSTerm>();
                final ArrayList<TRSTerm> argsr = new ArrayList<TRSTerm>();

                // **** LHS ****
                for (int j = 0; j < i; j++) {
                    argsf.add(TRSTerm.createVariable("x" + j));
                }

                // new function symbol
                final FunctionSymbol funSymf;
                if (i == fctA) {
                    funSymf = fct;
                } else {
                    funSymf = FunctionSymbol.create(name, i);
                    newSymbols.add(funSymf);
                }
                final TRSFunctionApplication funAppf =
                    TRSTerm.createFunctionApplication(funSymf, ImmutableCreator.create(argsf));
                argsl.add(funAppf);
                // **** RHS ****
                // args rhs -- one more than f from lhs
                argsr.addAll(argsf);
                for (int k = 1; k < appDummy.getArity(); k++) {
                    final TRSVariable new_x = TRSTerm.createVariable("y" + k);

                    // hinzufuegen zu LHS somit f(....), x_i+1
                    argsl.add(new_x);
                    argsr.add(new_x);
                }
                // rule lhs
                final TRSFunctionApplication lhs =
                    TRSTerm.createFunctionApplication(appDummy, ImmutableCreator.create(argsl));

                name = fg.getFreshName(fct.getName(), false);
                final FunctionSymbol funSymr = FunctionSymbol.create(name, argsr.size());
                newSymbols.add(funSymr);

                final TRSFunctionApplication rhs =
                    TRSTerm.createFunctionApplication(funSymr, ImmutableCreator.create(argsr));

                final Rule rule = Rule.create(lhs, rhs);

                u.add(rule);
            }
            informationSet.add(new Pair<>(fct,newSymbols));
        }

    }

    /**
     * computes the applicative arities for every FunctionSymbol Def. 8, page 3,
     * @param rules
     * @param map
     */
    public static void computeApplicativeArities(final Set<Rule> rules,
        final Map<FunctionSymbol, Integer> map,
        final boolean isP,
        final FunctionSymbol appSymbol, final UncurryMethod method) {
        // for all rules
        for (final Rule rule : rules) {
            // for all Terms of Rule
            for (final TRSTerm term : rule.getTerms()) {
                QDPUncurryingProcessor.computeApplicativeArities(term, map, isP, appSymbol, method);
            }
        }
    }

    private static void computeApplicativeArities(final TRSTerm term,
            final Map<FunctionSymbol, Integer> map,
            final boolean isP,
            final FunctionSymbol appSymbol, final UncurryMethod method) {
        final Triple<TRSTerm, FunctionSymbol[], TRSTerm[]> part = QDPUncurryingProcessor.partition(term, appSymbol, isP);
        final TRSTerm t = part.x;
        // insert in map
        if (Globals.useAssertions && !(method == UncurryMethod.GENERALIZED)) {
            assert (t.isConstant() || t.isVariable());
        }
        // first case: not general so should be constant
        // second case: general so should not be variable
        if ((t.isConstant() && !(method == UncurryMethod.GENERALIZED))
                || (!(t.isVariable()) && (method == UncurryMethod.GENERALIZED))) {
            final TRSFunctionApplication ft = (TRSFunctionApplication) t;
            final FunctionSymbol fSym = ft.getRootSymbol();
            final Integer mapForName = map.get(fSym);
            if (mapForName == null || mapForName < part.y.length) {
                map.put(fSym, part.y.length);
            }
        }
        // recurse into argument
        final boolean notP = false; // we are not at the root anymore.
        for (final TRSTerm arg : part.z) {
            QDPUncurryingProcessor.computeApplicativeArities(arg, map, notP, appSymbol, method);
        }
        if (!t.isVariable()) {
            final TRSFunctionApplication ft = (TRSFunctionApplication) t;
            for (final TRSTerm arg : ft.getArguments()) {
                QDPUncurryingProcessor.computeApplicativeArities(arg, map, notP, appSymbol, method);
            }
        }
    }


    /**
     * give aa = 1 for every function symbol that is the first argument of the
     * appSymbol
     *
     * @param rules
     * @param map
     */
    private static void computeApplicativeArities(final Set<Rule> rules,
        final Map<FunctionSymbol, Integer> map,
        final FunctionSymbol appSymbol) {
        // for all rules of qdp Problem
        for (final Rule rule : rules) {
            final TRSFunctionApplication lhs = rule.getLeft();
            if (!lhs.isVariable() && lhs.getRootSymbol().equals(appSymbol) && !lhs.isConstant()) {
                final TRSTerm term = lhs.getArgument(0);
                if (term instanceof TRSFunctionApplication) {
                    map.put(((TRSFunctionApplication) term).getRootSymbol(), 1);
                }
            }
            final TRSTerm rhs = rule.getRight();
            if (rhs instanceof TRSFunctionApplication) {
                final TRSFunctionApplication rhsApplication = (TRSFunctionApplication) rhs;
                if (!rhsApplication.isVariable() && rhsApplication.getRootSymbol().equals(appSymbol)
                    && !rhsApplication.isConstant()) {
                    final TRSTerm term = rhsApplication.getArgument(0);
                    if (term instanceof TRSFunctionApplication) {
                        map.put(((TRSFunctionApplication) term).getRootSymbol(), 1);
                    }
                }
            }
        }
    }

    /**
     * computes the applicative arity of a term, needs the applicative arities
     * of every FunctionSymbol
     * @param t term
     * @param map the applicative arities
     * @return applicative arity of the term
     */
    private static int getAATerm(final TRSTerm t, final Map<FunctionSymbol, Integer> map, final FunctionSymbol appDummy, final UncurryMethod method) {
        assert (!t.isVariable());

        final Triple<TRSTerm, FunctionSymbol[], TRSTerm[]> part = QDPUncurryingProcessor.partition(t, appDummy, false);

        if (Globals.useAssertions && !(method == UncurryMethod.GENERALIZED)) {
            assert (part.x.isConstant() || part.x.isVariable());
        }
        Integer aa;
        if ((part.x.isConstant() && !(method == UncurryMethod.GENERALIZED))
            || (!(part.x.isVariable()) && (method == UncurryMethod.GENERALIZED))) {
            final ArrayList<FunctionSymbol> fSyms = new ArrayList<FunctionSymbol>(part.x.getFunctionSymbols());
            final FunctionSymbol fSym = fSyms.get(0);
            aa = map.get(fSym);
        } else {
            aa = 0;
        }
        final Integer ai = part.y.length;
        return aa - ai;

    }

    /**
     * partitions a term x 'f_1 t_1 'f_2 ... 'f_n t_n into<br>
     * x,['f_1,'f_2,..,'f_n], [t_1,...,t_n]
     *
     * @param t
     * @return
     */
    private static Triple<TRSTerm, FunctionSymbol[], TRSTerm[]> partition(TRSTerm t, final FunctionSymbol appDummy, boolean isP) {
        if (t.isVariable()) {
            return new Triple<TRSTerm, FunctionSymbol[], TRSTerm[]>(t, new FunctionSymbol[0], new TRSTerm[0]);
        } else {
            int n = 0;
            TRSTerm s = t;
            TRSFunctionApplication fs = (TRSFunctionApplication) t;
            FunctionSymbol f = fs.getRootSymbol();
            // is applicable symbol
            while (f.equals(appDummy) || (isP && !fs.isConstant())) {
                n++;
                s = fs.getArgument(0);
                if (s.isVariable()) {
                    break;
                } else {
                    fs = (TRSFunctionApplication) s;
                    f = fs.getRootSymbol();
                }
                isP = false;
            }

            // now we have the arity and the left-most symbol
            final FunctionSymbol[] apSyms = new FunctionSymbol[n];
            final Set<TRSTerm> args = new LinkedHashSet<TRSTerm>();

            while (n > 0) {
                n--;
                fs = (TRSFunctionApplication) t;
                boolean first = true;
                apSyms[n] = fs.getRootSymbol();
                for (final TRSTerm term : fs.getArguments()) {
                    if (first) {
                        t = fs.getArgument(0);
                        first = false;
                    }
                    args.add(term);
                }
            }
            if (Globals.useAssertions) {
                assert (t.equals(s));
            }
            final TRSTerm[] argsarray = new TRSTerm[args.size()];
            int i = 0;
            for (final TRSTerm term : args) {
                argsarray[i++] = term;
            }
            final Triple<TRSTerm, FunctionSymbol[], TRSTerm[]> thePartition =
                new Triple<TRSTerm, FunctionSymbol[], TRSTerm[]>(s, apSyms, argsarray);
            return thePartition;
        }
    }

    /** Which method of uncurrying is used: **/
    public static enum UncurryMethod {
        /**
         * The normal method like it's done by Hirokawa, Middeldorp, Zankl in
         * 2008
         **/
        HIRO_MIDDEL_ZANKL,
        /** Improved/ generelized method by Thieman and Sternagl **/
        GENERALIZED;

        public String getName() {
            return this.toString();
        }
    }

    /** Which heuristic for the applicative arities is used: **/
    public static enum UncurryHeuristic {
        /**
         * formally: $\pi_+(f) = [f_0, \ldots, f_n]$ where $n$ is the maximal
         * number such that $f(\ldots) \circ t_1 \circ \ldots \circ t_n$ occurs
         * in $\mathcal R$
         */
        PLUS, // pi plus
        /**
         * formally: $\pi_\stacrel{+}{-}(f) = [f_0, \ldots, f_n]$ where $n =
         * min(aa_{\pi_+}(f), min\{k\mid f(\ldots) \circ t_1 \circ \ldots \circ
         * t_k \rightarrow r \in \mathcal R\})$ and no rules have to be added for
         * $\eta$-expansion
         */
        PLUS_MINUS; // pi plis minus

        public String getName() {
            return this.toString();
        }
    }

    public static class Arguments {
        /** Use the first technique that was implemented as default **/
        public UncurryMethod method = UncurryMethod.HIRO_MIDDEL_ZANKL;
        public boolean top = true; // use top-uncurrying
        public boolean noeta = true; // require that no rules have to added for eta-expansion
        public boolean applicativeSignature = true; // require that TRS only contains constants + exactly one binary symbol
        public boolean becomplete = true;
    }

    public static class QDPUncurryingProof extends QDPProof {
        private final QDPProblem newQDP;
        private final FunctionSymbol applicationSymbol;
        private final Set<Pair<FunctionSymbol, Set<FunctionSymbol>>> informationSet;
        private final Set<Rule> uncurriedRules;
        private final Set<Rule> etaRules;
        private final UncurryMethod method;
        private final boolean top;

        public QDPUncurryingProof(final QDPProblem newQDP,
                final FunctionSymbol applicationSymbol,
                final Set<Pair<FunctionSymbol, Set<FunctionSymbol>>> informationSet,
                final Set<Rule> uncurriedRules, final Set<Rule> etaRules, final UncurryMethod method, final boolean top) {
            this.newQDP = newQDP;
            this.applicationSymbol = applicationSymbol;
            this.informationSet = informationSet;
            this.uncurriedRules = uncurriedRules;
            this.etaRules = etaRules;
            this.method = method;
            this.top = top;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final QTRSProblem eta = QTRSProblem.create(ImmutableCreator.create(this.etaRules));
            final QTRSProblem uncurried = QTRSProblem.create(ImmutableCreator.create(this.uncurriedRules));
            return "The applicative DPProblem has been uncurried according to "
                + ((this.method == UncurryMethod.GENERALIZED) ? o.cite(new Citation[] {Citation.CSRT_FROCOS11 })
                    : o.cite(new Citation[] {Citation.NHAMHZ_LPAR08 })) + "." + o.linebreak() + o.cond_linebreak()
                + "The uncurried symbol is: " + this.applicationSymbol.export(o) + o.linebreak()
                + "The eta expanded rules are: " + o.linebreak() + eta.export(o) + "The uncurried rules are: "
                + o.linebreak() + uncurried.export(o) + o.cond_linebreak() + this.newQDP.export(o);
        }

        @Override
        public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
            if (modus.isPositive()) {
                final Element uncurry = CPFTag.UNCURRY_PROC.create(doc);
                if (this.top) {
                    uncurry.appendChild(CPFTag.APPLICATIVE_TOP.create(doc, this.applicationSymbol.getArity()));
                }
                uncurry.appendChild(QTRSUncurryingProcessor.uncurryInformation(
                                doc,
                                xmlMetaData,
                                this.applicationSymbol,
                                this.informationSet,
                                this.uncurriedRules,
                                this.etaRules));
                uncurry.appendChild(CPFTag.dps(doc, xmlMetaData, this.newQDP.getP()));
                uncurry.appendChild(CPFTag.trs(doc, xmlMetaData, this.newQDP.getR()));
                uncurry.appendChild(childrenProofs[0]);
                return this.positiveTag().create(doc, uncurry);
            } else {
                return super.toCPF(doc, childrenProofs, xmlMetaData, modus);
            }
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return modus.isPositive();
        }

    }
}
