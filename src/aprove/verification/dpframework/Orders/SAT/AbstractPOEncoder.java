package aprove.verification.dpframework.Orders.SAT;

import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.DPProblem.Processors.QDPSizeChangeProcessor.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.SAT.PLEncoders.*;
import aprove.verification.dpframework.Orders.SizeChangeNP.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.Variable;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.PropositionalLogic.ValueCaches.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public abstract class AbstractPOEncoder implements SATEncoder, SCNPOrderEncoder, SATSCTEncoder {

    public static Logger log = Logger.getLogger("aprove.verification.dpframework.Orders.SAT.AbstractPOEncoder");

    // formulaFactory must be a factory that does not incorporate the
    // argument list directly into the formula, but makes a copy instead
    protected FormulaFactory<None> formulaFactory;
    protected FactFactory factFactory;
    protected Constant<None> ZERO;
    protected Constant<None> ONE;
    protected SATPatterns<None> patterns;

    /**
     * Relations between terms that have been determined. Boolean.TRUE means
     * that s is greater than t while Boolean.FALSE means that s is greater or
     * equal to t.
     */
    private Map<Triple<TRSTerm, TRSTerm, ValueCache<None>>, Formula<None>> knownGENGR = new HashMap<Triple<TRSTerm, TRSTerm, ValueCache<None>>, Formula<None>>();
    /**
     * Relations between terms that have been determined. Boolean.TRUE means
     * that s is greater than t while Boolean.FALSE means that s is greater or
     * equal to t.
     */
    private Map<Triple<TRSTerm, TRSTerm, ValueCache<None>>, Formula<None>> knownGR = new HashMap<Triple<TRSTerm, TRSTerm, ValueCache<None>>, Formula<None>>();
    /**
     * Signature.
     */
    protected Set<FunctionSymbol> sig;
    /**
     * How many arguments can be regarded at one time? O encodes no limit.
     */
    private int restriction;

    /**
     * Cache already computed values of encodeRPOSLex
     * to avoid exponential blowup.
     */
    private Map<Triple<Integer, Triple<TRSFunctionApplication, TRSFunctionApplication, Boolean>, ValueCache<None>>, Formula<None>> knownQRPOSLex = new HashMap<Triple<Integer, Triple<TRSFunctionApplication, TRSFunctionApplication, Boolean>, ValueCache<None>>, Formula<None>>();
    /**
     * Cache already computed values of encodeRPOSLexEqual
     * to avoid exponential blowup.
     */
    private Map<Triple<Integer, Pair<TRSFunctionApplication, TRSFunctionApplication>, ValueCache<None>>, Formula<None>> knownQRPOSLexEqual = new HashMap<Triple<Integer, Pair<TRSFunctionApplication, TRSFunctionApplication>, ValueCache<None>>, Formula<None>>();

    /**
     * Cache already computed values of encodeRPOSLex
     * to avoid exponential blowup.
     */
    private Map<Triple<Integer, Triple<TRSFunctionApplication, TRSFunctionApplication, Boolean>, ValueCache<None>>, Formula<None>> knownRPOSLex = new HashMap<Triple<Integer, Triple<TRSFunctionApplication, TRSFunctionApplication, Boolean>, ValueCache<None>>, Formula<None>>();

    protected boolean quasi;
    protected boolean multiset;
    protected boolean lex;
    protected boolean perm;
    protected boolean prec;
    protected boolean xgengrc;
    protected AFSType afstype;

    // cache POFormula for avoiding recomputation of fact map
    private POFormula poFormula;
    // cache formula for knowing maxUsedVarId
    private Formula<None> formula;

    public AbstractPOEncoder(FormulaFactory<None> formulaFactory, boolean quasi, boolean multiset, boolean lex, boolean perm, boolean prec, boolean xgengrc, int restriction, AFSType afstype) {
        this.formulaFactory = formulaFactory;
        this.ZERO = formulaFactory.buildConstant(false);
        this.ONE = formulaFactory.buildConstant(true);
        this.factFactory = new FactFactory(formulaFactory);
        this.restriction = restriction;
        this.patterns = new SATPatterns<None>(formulaFactory, true);
        this.quasi = quasi;
        this.multiset = multiset;
        this.lex = lex;
        this.perm = perm;
        this.prec = prec;
        this.xgengrc = xgengrc;
    this.afstype = afstype;
    }

    protected Formula<None> encodeGRNonCollapsing(TRSTerm s, TRSFunctionApplication sApp, TRSTerm t, TRSFunctionApplication tApp, ValueCache<None> knownValues) {
        Formula<None> formula = this.encodeDisjunction(sApp, t, OrderRelation.GE, knownValues);
        if (formula == this.ONE) {
            return this.ONE;
        }
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        args.add(formula);
        FunctionSymbol f = sApp.getRootSymbol();
        FunctionSymbol g = tApp.getRootSymbol();
        List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
        if (!f.equals(g)) {
            List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
            Variable<None> varFSuccG = this.factFactory.getVarSucc(f,g);
            Formula<None> eVarFSuccG = varFSuccG.evaluate(knownValues);
            Variable<None> varFEqualG = this.factFactory.getVarEqual(f,g);
            Formula<None> eVarFEqualG = varFEqualG.evaluate(knownValues);
            if (this.prec && eVarFSuccG != this.ZERO && eVarFEqualG != this.ONE) {
                dArgs.add(eVarFSuccG);
            }
            if (this.quasi && eVarFSuccG != this.ONE && eVarFEqualG != this.ZERO) {
                ValueCache<None> newValues = knownValues.copy();
                NotFormula<None> notFSuccG = this.factFactory.getNotSucc(f, g);
                Formula<None> eNotFSuccG = notFSuccG.evaluate(knownValues);
                newValues.update(notFSuccG);
                newValues.update(varFEqualG);
                List<Formula<None>> bArgs = new ArrayList<Formula<None>>();
                bArgs.add(eNotFSuccG);
                bArgs.add(eVarFEqualG);
                bArgs.add(this.encodeQArgCompare(sApp, tApp, newValues));
                dArgs.add(this.formulaFactory.buildAnd(bArgs));
            }
            formula = this.formulaFactory.buildOr(dArgs);
        } else {
            formula = this.encodeArgCompare(sApp, tApp, knownValues);
        }
        if (formula != this.ZERO) {
            cArgs.add(formula);
            ValueCache<None> newValues = knownValues.copy();
            newValues.update(formula);
            cArgs.add(this.encodeConjunction(s, tApp, OrderRelation.GR, newValues));
            args.add(this.formulaFactory.buildAnd(cArgs));
        }
        return this.formulaFactory.buildOr(args);
    }

    protected Formula<None> encodeArgCompare(TRSFunctionApplication sApp, TRSFunctionApplication tApp, ValueCache<None> knownValues) {
        FunctionSymbol f = sApp.getRootSymbol();
        if (this.multiset && this.lex) {
            // we need a status bit per function symbol
            Variable<None> varStatusF = this.factFactory.getVarStatus(f);
            Formula<None> eVarStatusF = varStatusF.evaluate(knownValues);
            List<Formula<None>> args = new ArrayList<Formula<None>>();
            if (eVarStatusF != this.ZERO) {
                // multiset comparison possible
                List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
                cArgs.add(eVarStatusF);
                ValueCache<None> newValues = knownValues.copy();
                newValues.update(varStatusF);
                cArgs.add(this.encodeRPOSMulti(sApp, tApp, knownValues));
                args.add(this.formulaFactory.buildAnd(cArgs));
            }
            if (eVarStatusF != this.ONE) {
                // lexicographic comparison possible
                NotFormula<None> notStatusF = this.factFactory.getNotStatus(f);
                Formula<None> eNotStatusF = notStatusF.evaluate(knownValues);
                List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
                cArgs.add(eNotStatusF);
                ValueCache<None> newValues = knownValues.copy();
                newValues.update(notStatusF);
                cArgs.add(this.encodeRPOSLex(0, sApp, tApp, knownValues, false));
                args.add(this.formulaFactory.buildAnd(cArgs));
            }
            return this.formulaFactory.buildOr(args);
        } else {
            Formula<None> formula = null;
            if (this.multiset) {
                // only multiset comparison
                formula = this.encodeRPOSMulti(sApp, tApp, knownValues);
            }
            if (!this.multiset) {
                // lexicographic comparison if lex or simple otherwise
                formula = this.encodeRPOSLex(0, sApp, tApp, knownValues, false);
            }
            return formula;
        }
    }

    private Formula<None> encodeRPOSMulti(TRSFunctionApplication sApp, TRSFunctionApplication tApp, ValueCache<None> knownValues) {
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        FunctionSymbol f = sApp.getRootSymbol();
        if (Globals.useAssertions) {
            assert f.equals(tApp.getRootSymbol());
        }
        List<? extends TRSTerm> si = sApp.getArguments();
        List<? extends TRSTerm> ti = tApp.getArguments();
        int arity = f.getArity();
        NotFormula<None>[][] notSMultiEqT = this.factFactory.getNotMultiSuccEq(sApp, tApp);
        NotFormula<None>[][] notSMultiGrT = this.factFactory.getNotMultiSuccGr(sApp, tApp);
        for (int i = 0; i < arity; i++) {
            for (int j = 0; j < arity; j++) {
                Formula<None> eNotSMultiEqTIJ = notSMultiEqT[i][j].evaluate(knownValues);
                if (eNotSMultiEqTIJ != this.ONE) {
                    List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
                    dArgs.add(eNotSMultiEqTIJ);
                    ValueCache<None> newValues = knownValues.copy();
                    dArgs.add(this.encodeGENGR(si.get(i), ti.get(j), newValues));
                    args.add(this.formulaFactory.buildOr(dArgs));
                }
                Formula<None> eNotSMultiGrTIJ = notSMultiGrT[i][j].evaluate(knownValues);
                if (eNotSMultiGrTIJ != this.ONE) {
                    List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
                    dArgs.add(eNotSMultiGrTIJ);
                    ValueCache<None> newValues = knownValues.copy();
                    dArgs.add(this.encodeGR(si.get(i), ti.get(j), newValues));
                    args.add(this.formulaFactory.buildOr(dArgs));
                }
            }
        }
        // at least one greater!
        Variable<None>[][] varSMultiGr = this.factFactory.getVarMultiSuccGr(sApp, tApp);
        List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
        for (int i = 0; i < arity; i++) {
            for (int j = 0; j < arity; j++) {
                dArgs.add(varSMultiGr[i][j]);
            }
        }
        for (int i = 0; i < arity; i++) {
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            cArgs.add(this.factFactory.getVarArg(f, i));
            for (int j = 0; j < arity; j++) {
                cArgs.add(notSMultiEqT[i][j]);
            }
            dArgs.add(this.formulaFactory.buildAnd(cArgs));
        }
        args.add(this.formulaFactory.buildOr(dArgs));
        // encode constraints on gt and eq variables globally
        this.encodeMultiSuccGrEq(f, varSMultiGr, this.factFactory.getVarMultiSuccEq(sApp, tApp), args);
        return this.formulaFactory.buildAnd(args);
    }

    protected Formula<None> encodeRPOSLex(int k, TRSFunctionApplication sApp, TRSFunctionApplication tApp, ValueCache<None> knownValues, boolean haveGreater) {
        if (aprove.Globals.DEBUG_NOWONDER) {
            System.err.println(sApp+" "+k+" LexRPOS "+tApp);
        }
        Triple<Integer, Triple<TRSFunctionApplication, TRSFunctionApplication, Boolean>, ValueCache<None>> id = new Triple<Integer, Triple<TRSFunctionApplication, TRSFunctionApplication, Boolean>, ValueCache<None>>(k, new Triple<TRSFunctionApplication, TRSFunctionApplication, Boolean>(sApp, tApp, haveGreater), knownValues);
        Formula<None> knownResult = this.knownRPOSLex.get(id);
        if (knownResult != null) {
            if (aprove.Globals.DEBUG_NOWONDER) {
                System.err.println("REUSED CACHE");
            }
            return knownResult;
        }
        FunctionSymbol f = sApp.getRootSymbol();
        if (Globals.useAssertions) {
            assert f.equals(tApp.getRootSymbol());
        }
        int arity = f.getArity();
        if (!(k < arity)) {
            return this.updateRPOSLex(id, haveGreater ? this.ONE : this.ZERO);
        }
        List<? extends TRSTerm> si = sApp.getArguments();
        List<? extends TRSTerm> ti = tApp.getArguments();
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        for (int i = 0; i < arity; i++) {
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            Formula<None> varFPermIK = this.factFactory.getVarPerm(f, i, k);
            Formula<None> eVarFPermIK = varFPermIK.evaluate(knownValues);
            cArgs.add(eVarFPermIK);
            if (eVarFPermIK != this.ZERO) {
                Variable<None> varFArgI = this.factFactory.getVarArg(f, i);
                Formula<None> eVarFArgI = varFArgI.evaluate(knownValues);
                cArgs.add(eVarFArgI);
                if (eVarFArgI != this.ZERO) {
                    ValueCache<None> newValues = knownValues.copy();
                    newValues.update(varFPermIK);
                    newValues.update(varFArgI);
                    List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
                    Formula<None> formula = this.encodeGR(si.get(i), ti.get(i), newValues);
                    if (!this.lex) {
                        formula = this.formulaFactory.buildAnd(formula, this.encodeRPOSLex(k+1, sApp, tApp, knownValues, true));
                    }
                    dArgs.add(formula);
                    if (formula != this.ONE) {
                        List<Formula<None>> bArgs = new ArrayList<Formula<None>>();
                        formula = this.encodeGENGR(si.get(i), ti.get(i), newValues);
                        bArgs.add(formula);
                        if (formula != this.ZERO) {
                            // ValueCache<None> newerValues = newValues.copy();
                            // newerValues.update(formula);
                            bArgs.add(this.encodeRPOSLex(k+1, sApp, tApp, knownValues, haveGreater));
                        }
                        dArgs.add(this.formulaFactory.buildAnd(bArgs));
                    }
                    cArgs.add(this.formulaFactory.buildOr(dArgs));
                }
            }
            args.add(this.formulaFactory.buildAnd(cArgs));
        }
        return this.updateRPOSLex(id, this.formulaFactory.buildOr(args));
    }
    private Formula<None> updateRPOSLex(Triple<Integer, Triple<TRSFunctionApplication, TRSFunctionApplication, Boolean>, ValueCache<None>> id, Formula<None> formula) {
        if (aprove.Globals.DEBUG_NOWONDER) {
            System.err.println("Storing in Lex cache: "+id);
        }
        this.knownRPOSLex.put(id, formula);
        return formula;
    }

    private Formula<None> encodeQArgCompare(TRSFunctionApplication sApp, TRSFunctionApplication tApp, ValueCache<None> knownValues) {
        FunctionSymbol f = sApp.getRootSymbol();
        FunctionSymbol g = tApp.getRootSymbol();
        if (this.multiset && this.lex) {
            // we need a status bit per function symbol
            Variable<None> varStatusF = this.factFactory.getVarStatus(f);
            Formula<None> eVarStatusF = varStatusF.evaluate(knownValues);
            Variable<None> varStatusG = this.factFactory.getVarStatus(g);
            Formula<None> eVarStatusG = varStatusG.evaluate(knownValues);
            List<Formula<None>> args = new ArrayList<Formula<None>>();
            if (eVarStatusF != this.ZERO && eVarStatusG != this.ZERO) {
                // multiset comparison possible
                List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
                cArgs.add(eVarStatusF);
                cArgs.add(eVarStatusG);
                ValueCache<None> newValues = knownValues.copy();
                newValues.update(varStatusF);
                newValues.update(varStatusG);
                cArgs.add(this.encodeQRPOSMulti(sApp, tApp, knownValues));
                args.add(this.formulaFactory.buildAnd(cArgs));
            }
            if (eVarStatusF != this.ONE && eVarStatusG != this.ONE) {
                // lexicographic comparison possible
                NotFormula<None> notStatusF = this.factFactory.getNotStatus(f);
                Formula<None> eNotStatusF = notStatusF.evaluate(knownValues);
                NotFormula<None> notStatusG = this.factFactory.getNotStatus(g);
                Formula<None> eNotStatusG = notStatusG.evaluate(knownValues);
                List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
                cArgs.add(eNotStatusF);
                cArgs.add(eNotStatusG);
                ValueCache<None> newValues = knownValues.copy();
                newValues.update(notStatusF);
                newValues.update(notStatusG);
                cArgs.add(this.encodeQRPOSLex(0, sApp, tApp, knownValues, false));
                args.add(this.formulaFactory.buildAnd(cArgs));
            }
            return this.formulaFactory.buildOr(args);
        } else {
            Formula<None> formula = null;
            if (this.multiset) {
                // only multiset comparison
                formula = this.encodeQRPOSMulti(sApp, tApp, knownValues);
            }
            if (!this.multiset) {
                // lexicographic comparison if lex or simple otherwise
                formula = this.encodeQRPOSLex(0, sApp, tApp, knownValues, false);
            }
            return formula;
        }
    }

    private Formula<None> encodeQRPOSMulti(TRSFunctionApplication sApp, TRSFunctionApplication tApp, ValueCache<None> knownValues) {
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        FunctionSymbol f = sApp.getRootSymbol();
        FunctionSymbol g = tApp.getRootSymbol();
        List<? extends TRSTerm> si = sApp.getArguments();
        List<? extends TRSTerm> ti = tApp.getArguments();
        int fArity = f.getArity();
        int gArity = g.getArity();
        NotFormula<None>[][] notSMultiEqT = this.factFactory.getNotMultiSuccEq(sApp, tApp);
        NotFormula<None>[][] notSMultiGrT = this.factFactory.getNotMultiSuccGr(sApp, tApp);
        for (int i = 0; i < fArity; i++) {
            for (int j = 0; j < gArity; j++) {
                Formula<None> eNotSMultiEqTIJ = notSMultiEqT[i][j].evaluate(knownValues);
                if (eNotSMultiEqTIJ != this.ONE) {
                    List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
                    dArgs.add(eNotSMultiEqTIJ);
                    ValueCache<None> newValues = knownValues.copy();
                    dArgs.add(this.encodeGENGR(si.get(i), ti.get(j), newValues));
                    args.add(this.formulaFactory.buildOr(dArgs));
                }
                Formula<None> eNotSMultiGrTIJ = notSMultiGrT[i][j].evaluate(knownValues);
                if (eNotSMultiGrTIJ != this.ONE) {
                    List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
                    dArgs.add(eNotSMultiGrTIJ);
                    ValueCache<None> newValues = knownValues.copy();
                    dArgs.add(this.encodeGR(si.get(i), ti.get(j), newValues));
                    args.add(this.formulaFactory.buildOr(dArgs));
                }
            }
        }
        // at least one greater!
        Variable<None>[][] varSMultiGr = this.factFactory.getVarMultiSuccGr(sApp, tApp);
        List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
        for (int i = 0; i < fArity; i++) {
            for (int j = 0; j < gArity; j++) {
                dArgs.add(varSMultiGr[i][j]);
            }
        }
        for (int i = 0; i < fArity; i++) {
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            cArgs.add(this.factFactory.getVarArg(f, i));
            for (int j = 0; j < gArity; j++) {
                cArgs.add(notSMultiEqT[i][j]);
            }
            dArgs.add(this.formulaFactory.buildAnd(cArgs));
        }
        args.add(this.formulaFactory.buildOr(dArgs));
        // encode constraints on gt and eq variables globally
        this.encodeQMultiSuccGrEq(f, g, varSMultiGr, this.factFactory.getVarMultiSuccEq(sApp, tApp), args);
        return this.formulaFactory.buildAnd(args);
    }

    protected Formula<None> encodeQRPOSLex(int k, TRSFunctionApplication sApp, TRSFunctionApplication tApp, ValueCache<None> knownValues, boolean haveGreater) {
        if (aprove.Globals.DEBUG_NOWONDER) {
            System.err.println(sApp+" "+k+" LexQRPOS "+tApp);
        }
        Triple<Integer, Triple<TRSFunctionApplication, TRSFunctionApplication, Boolean>, ValueCache<None>> id = new Triple<Integer, Triple<TRSFunctionApplication, TRSFunctionApplication, Boolean>, ValueCache<None>>(k, new Triple<TRSFunctionApplication, TRSFunctionApplication, Boolean>(sApp, tApp, haveGreater), knownValues);
        Formula<None> knownResult = this.knownQRPOSLex.get(id);
        if (knownResult != null) {
            if (aprove.Globals.DEBUG_NOWONDER) {
                System.err.println("REUSED CACHE");
            }
            return knownResult;
        }
        FunctionSymbol f = sApp.getRootSymbol();
        FunctionSymbol g = tApp.getRootSymbol();
        int fArity = f.getArity();
        int gArity = g.getArity();
        if (!(k < fArity)) {
            return this.updateQRPOSLex(id, haveGreater && !(k < gArity) ? this.ONE : this.ZERO);
        }
        if (!(k < gArity)) {
            if (Options.certifier.isA3pat()) {
                return this.updateQRPOSLex(id, this.ZERO);
            }
            if (!this.lex) {
                return this.updateQRPOSLex(id, this.ZERO);
            }
            List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
            for (int i = 0; i < fArity; i++) {
                dArgs.add(this.formulaFactory.buildAnd(this.factFactory.getVarPerm(f, i, k).evaluate(knownValues), this.factFactory.getVarArg(f, i)));
            }
            return this.updateQRPOSLex(id, this.formulaFactory.buildOr(dArgs));
        }
        List<? extends TRSTerm> si = sApp.getArguments();
        List<? extends TRSTerm> ti = tApp.getArguments();
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        for (int i = 0; i < fArity; i++) {
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            Formula<None> varFPermIK = this.factFactory.getVarPerm(f, i, k);
            Formula<None> eVarFPermIK = varFPermIK.evaluate(knownValues);
            cArgs.add(eVarFPermIK);
            if (eVarFPermIK != this.ZERO) {
                Variable<None> varFArgI = this.factFactory.getVarArg(f, i);
                Formula<None> eVarFArgI = varFArgI.evaluate(knownValues);
                cArgs.add(eVarFArgI);
                if (eVarFArgI != this.ZERO) {
                    if (!this.lex) {
                        for (int j = 0; j < gArity; j++) {
                            Formula<None> varGPermJK = this.factFactory.getVarPerm(g, j, k);
                            Formula<None> eVarGPermJK = varGPermJK.evaluate(knownValues);
                            cArgs.add(eVarGPermJK);
                            if (eVarGPermJK != this.ZERO) {
                                Variable<None> varGArgJ = this.factFactory.getVarArg(g, j);
                                Formula<None> eVarGArgJ = varGArgJ.evaluate(knownValues);
                                cArgs.add(eVarGArgJ);
                                if (eVarGArgJ != this.ZERO) {
                                    ValueCache<None> newValues = knownValues.copy();
                                    newValues.update(varFPermIK);
                                    newValues.update(varFArgI);
                                    newValues.update(varGPermJK);
                                    newValues.update(varGArgJ);
                                    List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
                                    List<Formula<None>> aArgs = new ArrayList<Formula<None>>();
                                    Formula<None> formula = this.encodeGR(si.get(i), ti.get(j), newValues);
                                    aArgs.add(formula);
                                    if (formula != this.ZERO) {
                                        aArgs.add(this.encodeQRPOSLex(k+1, sApp, tApp, knownValues, true));
                                    }
                                    formula = this.formulaFactory.buildAnd(aArgs);
                                    dArgs.add(formula);
                                    if (formula != this.ONE) {
                                        List<Formula<None>> bArgs = new ArrayList<Formula<None>>();
                                        formula = this.encodeGENGR(si.get(i), ti.get(j), newValues);
                                        bArgs.add(formula);
                                        if (formula != this.ZERO) {
                                            bArgs.add(this.encodeQRPOSLex(k+1, sApp, tApp, knownValues, haveGreater));
                                        }
                                        dArgs.add(this.formulaFactory.buildAnd(bArgs));
                                    }
                                    cArgs.add(this.formulaFactory.buildOr(dArgs));
                                }
                            }
                        }
                    } else {
                        for (int j = 0; j < gArity; j++) {
                            List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
                            Formula<None> notGPermJK = this.factFactory.getNotPerm(g, j, k);
                            Formula<None> eNotGPermJK = notGPermJK.evaluate(knownValues);
                            dArgs.add(eNotGPermJK);
                            if (eNotGPermJK != this.ONE) {
                                NotFormula<None> notGArgJ = this.factFactory.getNotArg(g, j);
                                Formula<None> eNotGArgJ = notGArgJ.evaluate(knownValues);
                                dArgs.add(eNotGArgJ);
                                if (eNotGArgJ != this.ONE) {
                                    ValueCache<None> newValues = knownValues.copy();
                                    newValues.update(varFPermIK);
                                    newValues.update(varFArgI);
                                    Formula<None> varGPermJK = this.factFactory.getVarPerm(g, j, k);
                                    Variable<None> varGArgJ = this.factFactory.getVarArg(g, j);
                                    newValues.update(varGPermJK);
                                    newValues.update(varGArgJ);
                                    Formula<None> formula = this.encodeGR(si.get(i), ti.get(j), newValues);
                                    dArgs.add(formula);
                                    if (formula != this.ONE) {
                                        List<Formula<None>> bArgs = new ArrayList<Formula<None>>();
                                        formula = this.encodeGENGR(si.get(i), ti.get(j), newValues);
                                        bArgs.add(formula);
                                        if (formula != this.ZERO) {
                                            // ValueCache<None> newerValues = newValues.copy();
                                            // newerValues.update(formula);
                                            bArgs.add(this.encodeQRPOSLex(k+1, sApp, tApp, knownValues, haveGreater));
                                        }
                                        dArgs.add(this.formulaFactory.buildAnd(bArgs));
                                    }
                                }
                            }
                            cArgs.add(this.formulaFactory.buildOr(dArgs));
                        }
                    }
                }
            }
            args.add(this.formulaFactory.buildAnd(cArgs));
        }
        Formula<None> formula = this.formulaFactory.buildOr(args);
        return this.updateQRPOSLex(id, formula);
    }
    private Formula<None> updateQRPOSLex(Triple<Integer, Triple<TRSFunctionApplication, TRSFunctionApplication, Boolean>, ValueCache<None>> id, Formula<None> formula) {
        if (aprove.Globals.DEBUG_NOWONDER) {
            System.err.println("Storing in Lex cache: "+id);
        }
        this.knownQRPOSLex.put(id, formula);
        return formula;
    }


    protected Formula<None> encodeGENGRNonCollapsing(TRSTerm s, TRSFunctionApplication sApp, TRSTerm t, TRSFunctionApplication tApp, ValueCache<None> knownValues) {
        FunctionSymbol f = sApp.getRootSymbol();
        FunctionSymbol g = tApp.getRootSymbol();
        if (f.equals(g)) {
            return this.encodeArgCompareEqual(sApp, tApp, knownValues);
        }
        List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
        // f and g could be equal according to the precedence if g is not collapsing
        Variable<None> varEqualFG = this.factFactory.getVarEqual(f,g);
        Formula<None> eVarEqualFG = varEqualFG.evaluate(knownValues);
        Variable<None> varFlagG = this.factFactory.getVarFlag(g);
        Formula<None> eVarFlagG = varFlagG.evaluate(knownValues);
        if (this.quasi && eVarEqualFG != this.ZERO && eVarFlagG != this.ZERO) {
            ValueCache<None> newValues = knownValues.copy();
            newValues.update(varEqualFG);
            newValues.update(varFlagG);
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            cArgs.add(eVarEqualFG);
            cArgs.add(eVarFlagG);
            cArgs.add(this.encodeQArgCompareEqual(sApp, tApp, newValues));
            dArgs.add(this.formulaFactory.buildAnd(cArgs));
        }
        // collapsing g
        NotFormula<None> notFlagG = this.factFactory.getNotFlag(g);
        Formula<None> eNotFlagG = notFlagG.evaluate(knownValues);
        if (eNotFlagG != this.ZERO) {
            ValueCache<None> newValues = knownValues.copy();
            newValues.update(notFlagG);
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            cArgs.add(eNotFlagG);
            cArgs.add(this.encodeConjunction(s, tApp, OrderRelation.GENGR, newValues));
            dArgs.add(this.formulaFactory.buildAnd(cArgs));
        }
        return this.formulaFactory.buildOr(dArgs);
    }

    protected Formula<None> encodeArgCompareEqual(TRSFunctionApplication sApp, TRSFunctionApplication tApp, ValueCache<None> knownValues) {
        FunctionSymbol f = sApp.getRootSymbol();
        if (this.multiset && this.lex) {
            // we need a status bit per function symbol
            Variable<None> varStatusF = this.factFactory.getVarStatus(f);
            Formula<None> eVarStatusF = varStatusF.evaluate(knownValues);
            List<Formula<None>> args = new ArrayList<Formula<None>>();
            if (this.multiset && eVarStatusF != this.ZERO) {
                // multiset comparison possible
                List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
                cArgs.add(eVarStatusF);
                ValueCache<None> newValues = knownValues.copy();
                newValues.update(varStatusF);
                cArgs.add(this.encodeRPOSMultiEqual(sApp, tApp, knownValues));
                args.add(this.formulaFactory.buildAnd(cArgs));
            }
            if (this.lex && eVarStatusF != this.ONE) {
                // lexicographic comparison possible
                NotFormula<None> notStatusF = this.factFactory.getNotStatus(f);
                Formula<None> eNotStatusF = notStatusF.evaluate(knownValues);
                List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
                cArgs.add(eNotStatusF);
                ValueCache<None> newValues = knownValues.copy();
                newValues.update(notStatusF);
                cArgs.add(this.encodeRPOSLexEqual(sApp, tApp, knownValues));
                args.add(this.formulaFactory.buildAnd(cArgs));
            }
            return this.formulaFactory.buildOr(args);
        } else {
            Formula<None> formula = null;
            if (this.multiset) {
                // only multiset comparison
                formula = this.encodeRPOSMultiEqual(sApp, tApp, knownValues);
            }
            if (!this.multiset) {
                // lexicographic comparison
                formula = this.encodeRPOSLexEqual(sApp, tApp, knownValues);
            }
            return formula;
        }
    }

    protected Formula<None> encodeRPOSMultiEqual(TRSFunctionApplication sApp, TRSFunctionApplication tApp, ValueCache<None> knownValues) {
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        FunctionSymbol f = sApp.getRootSymbol();
        if (Globals.useAssertions) {
            assert f.equals(tApp.getRootSymbol());
        }
        List<? extends TRSTerm> si = sApp.getArguments();
        List<? extends TRSTerm> ti = tApp.getArguments();
        int arity = f.getArity();
        NotFormula<None>[][] notSMultiSimEqT = this.factFactory.getNotMultiSimEq(sApp, tApp);
        for (int i = 0; i < arity; i++) {
            for (int j = 0; j < arity; j++) {
                Formula<None> eNotSMultiSimEqTIJ = notSMultiSimEqT[i][j].evaluate(knownValues);
                if (eNotSMultiSimEqTIJ != this.ONE) {
                    List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
                    dArgs.add(eNotSMultiSimEqTIJ);
                    ValueCache<None> newValues = knownValues.copy();
                    dArgs.add(this.encodeGENGR(si.get(i), ti.get(j), newValues));
                    args.add(this.formulaFactory.buildOr(dArgs));
                }
            }
        }
        this.encodeMultiSimEq(f, this.factFactory.getVarMultiSimEq(sApp, tApp), args);
        return this.formulaFactory.buildAnd(args);
    }

    protected Formula<None> encodeRPOSLexEqual(TRSFunctionApplication sApp, TRSFunctionApplication tApp, ValueCache<None> knownValues) {
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        FunctionSymbol f = sApp.getRootSymbol();
        if (Globals.useAssertions) {
            assert f.equals(tApp.getRootSymbol());
        }
        List<? extends TRSTerm> si = sApp.getArguments();
        List<? extends TRSTerm> ti = tApp.getArguments();
        int arity = f.getArity();
        for (int i = 0; i < arity; i++) {
            List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
            dArgs.add(this.factFactory.getNotArg(f, i));
            dArgs.add(this.encodeGENGR(si.get(i), ti.get(i), knownValues));
            args.add(this.formulaFactory.buildOr(dArgs));
        }
        return this.formulaFactory.buildAnd(args);
    }

    protected Formula<None> encodeQArgCompareEqual(TRSFunctionApplication sApp, TRSFunctionApplication tApp, ValueCache<None> knownValues) {
        FunctionSymbol f = sApp.getRootSymbol();
        FunctionSymbol g = tApp.getRootSymbol();
        if (this.multiset && this.lex) {
            // we need a status bit per function symbol
            Variable<None> varStatusF = this.factFactory.getVarStatus(f);
            Formula<None> eVarStatusF = varStatusF.evaluate(knownValues);
            Variable<None> varStatusG = this.factFactory.getVarStatus(g);
            Formula<None> eVarStatusG = varStatusG.evaluate(knownValues);
            List<Formula<None>> args = new ArrayList<Formula<None>>();
            if (this.multiset && eVarStatusF != this.ZERO && eVarStatusG != this.ZERO) {
                // multiset comparison possible
                List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
                cArgs.add(eVarStatusF);
                cArgs.add(eVarStatusG);
                ValueCache<None> newValues = knownValues.copy();
                newValues.update(varStatusF);
                newValues.update(varStatusG);
                cArgs.add(this.encodeQRPOSMultiEqual(sApp, tApp, knownValues));
                args.add(this.formulaFactory.buildAnd(cArgs));
            }
            if (this.lex && eVarStatusF != this.ONE && eVarStatusG != this.ONE) {
                // lexicographic comparison possible
                NotFormula<None> notStatusF = this.factFactory.getNotStatus(f);
                Formula<None> eNotStatusF = notStatusF.evaluate(knownValues);
                NotFormula<None> notStatusG = this.factFactory.getNotStatus(g);
                Formula<None> eNotStatusG = notStatusG.evaluate(knownValues);
                List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
                cArgs.add(eNotStatusF);
                cArgs.add(eNotStatusG);
                ValueCache<None> newValues = knownValues.copy();
                newValues.update(notStatusF);
                newValues.update(notStatusG);
                cArgs.add(this.encodeQRPOSLexEqual(0, sApp, tApp, knownValues));
                args.add(this.formulaFactory.buildAnd(cArgs));
            }
            return this.formulaFactory.buildOr(args);
        } else {
            Formula<None> formula = null;
            if (this.multiset) {
                // only multiset comparison
                formula = this.encodeQRPOSMultiEqual(sApp, tApp, knownValues);
            }
            if (!this.multiset) {
                // only lexicographic comparison
                formula = this.encodeQRPOSLexEqual(0, sApp, tApp, knownValues);
            }
            return formula;
        }
    }

    protected Formula<None> encodeQRPOSMultiEqual(TRSFunctionApplication sApp, TRSFunctionApplication tApp, ValueCache<None> knownValues) {
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        FunctionSymbol f = sApp.getRootSymbol();
        FunctionSymbol g = tApp.getRootSymbol();
        List<? extends TRSTerm> si = sApp.getArguments();
        List<? extends TRSTerm> ti = tApp.getArguments();
        int fArity = f.getArity();
        int gArity = g.getArity();
        NotFormula<None>[][] notSMultiSimEqT = this.factFactory.getNotMultiSimEq(sApp, tApp);
        for (int i = 0; i < fArity; i++) {
            for (int j = 0; j < gArity; j++) {
                Formula<None> eNotSMultiSimEqTIJ = notSMultiSimEqT[i][j].evaluate(knownValues);
                if (eNotSMultiSimEqTIJ != this.ONE) {
                    List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
                    dArgs.add(eNotSMultiSimEqTIJ);
                    ValueCache<None> newValues = knownValues.copy();
                    dArgs.add(this.encodeGENGR(si.get(i), ti.get(j), newValues));
                    args.add(this.formulaFactory.buildOr(dArgs));
                }
            }
        }
        this.encodeQMultiSimEq(f, g, this.factFactory.getVarMultiSimEq(sApp, tApp), args);
        return this.formulaFactory.buildAnd(args);
    }

    protected Formula<None> encodeQRPOSLexEqual(int k, TRSFunctionApplication sApp, TRSFunctionApplication tApp, ValueCache<None> knownValues) {
        if (aprove.Globals.DEBUG_NOWONDER) {
            System.err.println(sApp+" "+k+" LexQRPOSEqual "+tApp);
        }
        Triple<Integer, Pair<TRSFunctionApplication, TRSFunctionApplication>, ValueCache<None>> id = new Triple<Integer, Pair<TRSFunctionApplication, TRSFunctionApplication>, ValueCache<None>>(k, new Pair<TRSFunctionApplication, TRSFunctionApplication>(sApp, tApp), knownValues);
        Formula<None> knownResult = this.knownQRPOSLexEqual.get(id);
        if (knownResult != null) {
            if (aprove.Globals.DEBUG_NOWONDER) {
                System.err.println("REUSED CACHE");
            }
            return knownResult;
        }
        FunctionSymbol f = sApp.getRootSymbol();
        FunctionSymbol g = tApp.getRootSymbol();
        int fArity = f.getArity();
        int gArity = g.getArity();
        if (!(k < fArity)) {
            if (!(k < gArity)) {
                return this.updateQRPOSLexEqual(id, this.ONE);
            }
            List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
            for (int j = 0; j < gArity; j++) {
                dArgs.add(this.formulaFactory.buildAnd(this.factFactory.getVarPerm(g, j, k).evaluate(knownValues),this.factFactory.getVarArg(g, j)));
            }
            return this.updateQRPOSLexEqual(id, this.formulaFactory.buildNot(this.formulaFactory.buildOr(dArgs)));
        }
        if (!(k < gArity)) {
            List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
            for (int i = 0; i < fArity; i++) {
                dArgs.add(this.formulaFactory.buildAnd(this.factFactory.getVarPerm(f, i, k).evaluate(knownValues),this.factFactory.getVarArg(f, i)));
            }
            return this.updateQRPOSLexEqual(id, this.formulaFactory.buildNot(this.formulaFactory.buildOr(dArgs)));
        }
        List<? extends TRSTerm> si = sApp.getArguments();
        List<? extends TRSTerm> ti = tApp.getArguments();
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        for (int i = 0; i < fArity; i++) {
            List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
            Formula<None> notFPermIK = this.factFactory.getNotPerm(f, i, k);
            Formula<None> eNotFPermIK = notFPermIK.evaluate(knownValues);
            dArgs.add(eNotFPermIK);
            if (eNotFPermIK != this.ONE) {
                NotFormula<None> notFArgI = this.factFactory.getNotArg(f, i);
                Formula<None> eNotFArgI = notFArgI.evaluate(knownValues);
                dArgs.add(eNotFArgI);
                if (eNotFArgI != this.ONE) {
                    for (int j = 0; j < gArity; j++) {
                        List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
                        Formula<None> varGPermJK = this.factFactory.getVarPerm(g, j, k);
                        Formula<None> eVarGPermJK = varGPermJK.evaluate(knownValues);
                        cArgs.add(eVarGPermJK);
                        if (eVarGPermJK != this.ZERO) {
                            Variable<None> varGArgJ = this.factFactory.getVarArg(g, j);
                            Formula<None> eVarGArgJ = varGArgJ.evaluate(knownValues);
                            cArgs.add(eVarGArgJ);
                        }
                        dArgs.add(this.formulaFactory.buildAnd(cArgs));
                    }
                }
            }
            args.add(this.formulaFactory.buildOr(dArgs));
        }
        for (int j = 0; j < gArity; j++) {
            List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
            Formula<None> notGPermJK = this.factFactory.getNotPerm(g, j, k);
            Formula<None> eNotGPermJK = notGPermJK.evaluate(knownValues);
            dArgs.add(eNotGPermJK);
            if (eNotGPermJK != this.ONE) {
                NotFormula<None> notGArgJ = this.factFactory.getNotArg(g, j);
                Formula<None> eNotGArgJ = notGArgJ.evaluate(knownValues);
                dArgs.add(eNotGArgJ);
                if (eNotGArgJ != this.ONE) {
                    for (int i = 0; i < fArity; i++) {
                        List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
                        Formula<None> varFPermIK = this.factFactory.getVarPerm(f, i, k);
                        Formula<None> eVarFPermIK = varFPermIK.evaluate(knownValues);
                        cArgs.add(eVarFPermIK);
                        if (eVarFPermIK != this.ZERO) {
                            Variable<None> varFArgI = this.factFactory.getVarArg(f, i);
                            Formula<None> eVarFArgI = varFArgI.evaluate(knownValues);
                            cArgs.add(eVarFArgI);
                        }
                        dArgs.add(this.formulaFactory.buildAnd(cArgs));
                    }
                }
            }
            args.add(this.formulaFactory.buildOr(dArgs));
        }
        for (int i = 0; i < fArity; i++) {
            for (int j = 0; j < gArity; j++) {
                List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
                Formula<None> notFPermIK = this.factFactory.getNotPerm(f,i,k);
                Formula<None> eNotFPermIK = notFPermIK.evaluate(knownValues);
                dArgs.add(this.formulaFactory.buildOr(eNotFPermIK, this.factFactory.getNotArg(f, i)));
                if (eNotFPermIK != this.ONE) {
                    Formula<None> notGPermJK = this.factFactory.getNotPerm(g,j,k);
                    Formula<None> eNotGPermJK = notGPermJK.evaluate(knownValues);
                    dArgs.add(this.formulaFactory.buildOr(eNotGPermJK,this.factFactory.getNotArg(g, j)));
                    if (eNotGPermJK != this.ONE) {
                        dArgs.add(this.encodeGENGR(si.get(i), ti.get(j), knownValues));
                    }
                }
                args.add(this.formulaFactory.buildOr(dArgs));
            }
        }
        args.add(this.encodeQRPOSLexEqual(k+1, sApp, tApp, knownValues));
        return this.updateQRPOSLexEqual(id, this.formulaFactory.buildAnd(args));
    }
    private Formula<None> updateQRPOSLexEqual(Triple<Integer, Pair<TRSFunctionApplication, TRSFunctionApplication>, ValueCache<None>> id, Formula<None> formula) {
        if (aprove.Globals.DEBUG_NOWONDER) {
            System.err.println("Storing in Lex cache: "+id);
        }
        this.knownQRPOSLexEqual.put(id, formula);
        return formula;
    }

    protected Formula<None> encodePermutationConstraints(ValueCache<None> knownValues) {
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        for (Map.Entry<FunctionSymbol, Variable<None>[][]> entry : this.factFactory.getVarPerm().entrySet()) {
            FunctionSymbol f = entry.getKey();
            int arity = f.getArity();
            Variable<None>[] varArgs = this.factFactory.getVarArgs(f);
            NotFormula<None>[] notArgs = this.factFactory.getNotArgs(f);
            Variable<None>[][] vars = entry.getValue();
            Variable<None>[][] tVars = new Variable[arity][arity];
            for (int i = 0; i < arity; i++) {
                for (int j = 0; j < arity; j++) {
                    tVars[j][i] = vars[i][j];
                }
            }
            for (int i = 0; i < arity; i++) {
                args.add(this.patterns.encodeExactlyOne(vars[i]));
            }
            for (int k = 0; k < arity; k++) {
                args.add(this.patterns.encodeExactlyOne(tVars[k]));
                if (k > 0) {
                    for (int i = 0; i < arity; i++) {
                        List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
                        dArgs.add(this.formulaFactory.buildNot(vars[i][k]));
                        dArgs.add(notArgs[i]);
                        int bound = this.perm ? arity : i;
                        for (int j = 0; j < bound; j++) {
                            dArgs.add(this.formulaFactory.buildAnd(vars[j][k-1], varArgs[j]));
                        }
                        args.add(this.formulaFactory.buildOr(dArgs));
                    }
                }
            }
        }
        return this.formulaFactory.buildAnd(args);
    }

    public void encodeMultiSimEq(FunctionSymbol f, Variable<None>[][] vars, List<Formula<None>> args) {
        int arity = f.getArity();
        Variable<None>[] varArgs = this.factFactory.getVarArgs(f);
        NotFormula<None>[] notArgs = this.factFactory.getNotArgs(f);
        Variable<None>[][] tVars = new Variable[arity][arity];
        for (int i = 0; i < arity; i++) {
            for (int j = 0; j < arity; j++) {
                tVars[j][i] = vars[i][j];
            }
        }
        for (int i = 0; i < arity; i++) {
            List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
            dArgs.add(notArgs[i]);
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            cArgs.add(this.patterns.encodeExactlyOne(vars[i]));
            cArgs.add(this.patterns.encodeExactlyOne(tVars[i]));
            dArgs.add(this.formulaFactory.buildAnd(cArgs));
            args.add(this.formulaFactory.buildOr(dArgs));
            dArgs.clear();
            dArgs.add(varArgs[i]);
            cArgs.clear();
            cArgs.add(this.patterns.encodeNone(vars[i]));
            cArgs.add(this.patterns.encodeNone(tVars[i]));
            dArgs.add(this.formulaFactory.buildAnd(cArgs));
            args.add(this.formulaFactory.buildOr(dArgs));
        }
    }

    public void encodeMultiSuccGrEq(FunctionSymbol f, Variable<None>[][] varsGr, Variable<None>[][] varsEq, List<Formula<None>> args) {
        int arity = f.getArity();
        Variable<None>[] varArgs = this.factFactory.getVarArgs(f);
        NotFormula<None>[] notArgs = this.factFactory.getNotArgs(f);
        Variable<None>[][] tVarsGr = new Variable[arity][arity];
        for (int i = 0; i < arity; i++) {
            for (int j = 0; j < arity; j++) {
                tVarsGr[j][i] = varsGr[i][j];
            }
        }
        Variable<None>[][] tVarsEq = new Variable[arity][arity];
        for (int i = 0; i < arity; i++) {
            for (int j = 0; j < arity; j++) {
                tVarsEq[j][i] = varsEq[i][j];
            }
        }
        for (int i = 0; i < arity; i++) {
            List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
            dArgs.add(this.patterns.encodeNone(varsEq[i]));
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            cArgs.add(this.patterns.encodeExactlyOne(varsEq[i]));
            cArgs.add(this.patterns.encodeNone(varsGr[i]));
            dArgs.add(this.formulaFactory.buildAnd(cArgs));
            args.add(this.formulaFactory.buildOr(dArgs));
            dArgs.clear();
            dArgs.add(varArgs[i]);
            cArgs.clear();
            cArgs.add(this.patterns.encodeNone(varsEq[i]));
            cArgs.add(this.patterns.encodeNone(tVarsEq[i]));
            cArgs.add(this.patterns.encodeNone(varsGr[i]));
            cArgs.add(this.patterns.encodeNone(tVarsGr[i]));
            dArgs.add(this.formulaFactory.buildAnd(cArgs));
            args.add(this.formulaFactory.buildOr(dArgs));
            dArgs.clear();
            dArgs.add(notArgs[i]);
            for (int j = 0; j < arity; j++) {
                dArgs.add(varsEq[j][i]);
                dArgs.add(varsGr[j][i]);
            }
            args.add(this.formulaFactory.buildOr(dArgs));
        }
    }

    public void encodeQMultiSimEq(FunctionSymbol f, FunctionSymbol g, Variable<None>[][] vars, List<Formula<None>> args) {
        int fArity = f.getArity();
        int gArity = g.getArity();
        Variable<None>[] varFArgs = this.factFactory.getVarArgs(f);
        NotFormula<None>[] notFArgs = this.factFactory.getNotArgs(f);
        Variable<None>[] varGArgs = this.factFactory.getVarArgs(g);
        NotFormula<None>[] notGArgs = this.factFactory.getNotArgs(g);
        Variable<None>[][] tVars = new Variable[gArity][fArity];
        for (int i = 0; i < fArity; i++) {
            for (int j = 0; j < gArity; j++) {
                tVars[j][i] = vars[i][j];
            }
        }
        for (int i = 0; i < fArity; i++) {
            List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
            dArgs.add(notFArgs[i]);
            dArgs.add(this.patterns.encodeExactlyOne(vars[i]));
            args.add(this.formulaFactory.buildOr(dArgs));
            dArgs.clear();
            dArgs.add(varFArgs[i]);
            dArgs.add(this.patterns.encodeNone(vars[i]));
            args.add(this.formulaFactory.buildOr(dArgs));
        }
        for (int j = 0; j < gArity; j++) {
            List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
            dArgs.add(notGArgs[j]);
            dArgs.add(this.patterns.encodeExactlyOne(tVars[j]));
            args.add(this.formulaFactory.buildOr(dArgs));
            dArgs.clear();
            dArgs.add(varGArgs[j]);
            dArgs.add(this.patterns.encodeNone(tVars[j]));
            args.add(this.formulaFactory.buildOr(dArgs));
        }
    }

    public void encodeQMultiSuccGrEq(FunctionSymbol f, FunctionSymbol g, Variable<None>[][] varsGr, Variable<None>[][] varsEq, List<Formula<None>> args) {
        int fArity = f.getArity();
        int gArity = g.getArity();
        Variable<None>[] varFArgs = this.factFactory.getVarArgs(f);
        Variable<None>[] varGArgs = this.factFactory.getVarArgs(g);
        NotFormula<None>[] notGArgs = this.factFactory.getNotArgs(g);
        Variable<None>[][] tVarsGr = new Variable[gArity][fArity];
        for (int i = 0; i < fArity; i++) {
            for (int j = 0; j < gArity; j++) {
                tVarsGr[j][i] = varsGr[i][j];
            }
        }
        Variable<None>[][] tVarsEq = new Variable[gArity][fArity];
        for (int i = 0; i < fArity; i++) {
            for (int j = 0; j < gArity; j++) {
                tVarsEq[j][i] = varsEq[i][j];
            }
        }
        for (int i = 0; i < fArity; i++) {
            List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
            dArgs.add(this.patterns.encodeNone(varsEq[i]));
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            cArgs.add(this.patterns.encodeExactlyOne(varsEq[i]));
            cArgs.add(this.patterns.encodeNone(varsGr[i]));
            dArgs.add(this.formulaFactory.buildAnd(cArgs));
            args.add(this.formulaFactory.buildOr(dArgs));
            dArgs.clear();
            dArgs.add(varFArgs[i]);
            cArgs.clear();
            cArgs.add(this.patterns.encodeNone(varsEq[i]));
            cArgs.add(this.patterns.encodeNone(varsGr[i]));
            dArgs.add(this.formulaFactory.buildAnd(cArgs));
            args.add(this.formulaFactory.buildOr(dArgs));
        }
        for (int j = 0; j < gArity; j++) {
            List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
            dArgs.add(notGArgs[j]);
            for (int i = 0; i < fArity; i++) {
                dArgs.add(varsEq[i][j]);
                dArgs.add(varsGr[i][j]);
            }
            args.add(this.formulaFactory.buildOr(dArgs));
            dArgs.clear();
            dArgs.add(varGArgs[j]);
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            cArgs.add(this.patterns.encodeNone(tVarsEq[j]));
            cArgs.add(this.patterns.encodeNone(tVarsGr[j]));
            dArgs.add(this.formulaFactory.buildAnd(cArgs));
            args.add(this.formulaFactory.buildOr(dArgs));
        }
    }

    public Qoset<FunctionSymbol> getQoset(Set<Variable<None>> knownTrue, Afs afs) {
        Map<FunctionSymbol, FunctionSymbol> symbolMap = afs.getSymbolMap(this.sig);
        Qoset<FunctionSymbol> qoset = Qoset.create(symbolMap.values());
        try {
            for (Map.Entry<FunctionSymbol, FunctionSymbol> entryF : symbolMap.entrySet()) {
                FunctionSymbol f = entryF.getKey();
                FunctionSymbol filteredF = entryF.getValue();
                if (knownTrue.contains(this.factFactory.getVarBot(f))) {
                    qoset.setMinimal(filteredF);
                }
                for (Map.Entry<FunctionSymbol, FunctionSymbol> entryG : symbolMap.entrySet()) {
                    FunctionSymbol g = entryG.getKey();
                    if (knownTrue.contains(this.factFactory.getVarSucc(f,g))) {
                        FunctionSymbol filteredG = entryG.getValue();
                        qoset.setGreater(filteredF, filteredG);
                    }
                    if (knownTrue.contains(this.factFactory.getVarEqual(f,g))) {
                        FunctionSymbol filteredG = entryG.getValue();
                        qoset.setEquivalent(filteredF, filteredG);
                    }
                }
            }
            qoset.fix();
        } catch (OrderedSetException e) {
            e.printStackTrace();
            assert false : e.getMessage();
        }
        return qoset;
    }

    public Poset<FunctionSymbol> getPoset(Set<Variable<None>> knownTrue, Afs afs) {
        Map<FunctionSymbol, FunctionSymbol> symbolMap = afs.getSymbolMap(this.sig);
        Poset<FunctionSymbol> poset = Poset.create(symbolMap.values());
        try {
            for (Map.Entry<FunctionSymbol, FunctionSymbol> entryF : symbolMap.entrySet()) {
                FunctionSymbol f = entryF.getKey();
                FunctionSymbol filteredF = entryF.getValue();
                if (knownTrue.contains(this.factFactory.getVarBot(f))) {
                    poset.setMinimal(filteredF);
                }
                for (Map.Entry<FunctionSymbol, FunctionSymbol> entryG : symbolMap.entrySet()) {
                    FunctionSymbol g = entryG.getKey();
                    if (knownTrue.contains(this.factFactory.getVarSucc(f,g))) {
                        FunctionSymbol filteredG = entryG.getValue();
                        poset.setGreater(filteredF, filteredG);
                    }
                }
            }
        } catch (OrderedSetException e) {
            e.printStackTrace();
            assert false : e.getMessage();
        }
        return poset;
    }

    public StatusMap<FunctionSymbol> getStatusMap(Set<Variable<None>> knownTrue, Afs afs) {
        Map<FunctionSymbol, FunctionSymbol> symbolMap = afs.getSymbolMap(this.sig);
        StatusMap<FunctionSymbol> statusMap = StatusMap.create(symbolMap.values());
        for (Map.Entry<FunctionSymbol, FunctionSymbol> entryF : symbolMap.entrySet()) {
            FunctionSymbol f = entryF.getKey();
            FunctionSymbol filteredF = entryF.getValue();
            if (knownTrue.contains(this.factFactory.getVarStatus(f))) {
                // multiset comparison
                statusMap.assignMultisetStatus(filteredF);
            } else {
                // lexicographic comparision w.r.t. permutation
                int arity = f.getArity();
                int filteredArity = filteredF.getArity();
                int[] filteredP = new int[filteredArity];
                Variable<None>[][] vars;
                vars = this.factFactory.getVarPerm().get(f);
                if (vars == null) {
                    if (this.multiset) {
                        // fine, no one cared for the arguments
                        // just make this a multiset comparison
                        statusMap.assignMultisetStatus(filteredF);
                    } else {
                        // no multiset comparison available
                        // construct identity permutation
                        for (int i = 0; i < filteredArity; i++) {
                            filteredP[i] = i;
                        }
                        Permutation perm = Permutation.create(filteredP);
                        statusMap.assignPermutation(filteredF, perm);
                    }
                       continue;
                }
                for (int i = 0; i < arity; i++) {
                    for (int j = 0; j < filteredArity; j++) {
                        if (knownTrue.contains(vars[i][j])) {
                            filteredP[j] = i;
                            break;
                        }
                    }
                }
                if (Globals.DEBUG_NOWONDER) {
                    System.out.println(f);
                    for (int i = 0; i < filteredArity; i++) {
                        System.out.println(filteredP[i]);
                    }
                }
                int[] old2newIndices = new int[arity];
                Variable<None>[] varArgs = this.factFactory.getVarArgs(f);
                int j = 0;
                for (int i = 0; i < arity; i++) {
                    if (knownTrue.contains(varArgs[i])) {
                        old2newIndices[i] = j;
                        j++;
                    }
                }
                for (int i = 0; i < filteredArity; i++) {
                    filteredP[i] = old2newIndices[filteredP[i]];
                }
                if (Globals.DEBUG_NOWONDER) {
                    System.out.println(f);
                    for (int i = 0; i < filteredArity; i++) {
                        System.out.println(filteredP[i]);
                    }
                }
                Permutation perm = Permutation.create(filteredP);
                statusMap.assignPermutation(filteredF, perm);
            }
        }
        return statusMap;
    }

    /**
     * <pre>
encode(S,N,Constraint) :-
        retractall(lemma_gt_lpo(_,_,_,_)),
        encode_part1(S,N,True,C1),
        (C1==0 -> C2=0 ;
            update(C1,True,True1),
            encode_part2(S,True1,C2)
        ),
        simplify(C1*C2,Constraint),
        prettyprint(Constraint, True1).

% to encode dependency pair problem S,N:
%  part1 *C0 the global parts
%  part1 *C1 for every nonstrict rule in N, s -> t, we have s >= t
%  part1 *C2 for every strict rule s -> t in S, we have s > t or s >= t
%  part2 *C3 for at least one strict rule in S, s -> t, we have s > t

encode_part1(S,N,True,Constraint) :-
        global(S,N,True1,C1),
        forall_ns_lpo(S,True1,C2),
        simplify(C1*C2,T1),
        (T1==0 -> C3=0, True=[] ;
            update(T1,True1,True),
            forall_ns_lpo(N,True,C3)
        ),
        simplify(T1*C3,Constraint).

encode_part2(S,True,Constraint) :-
        exists_s_lpo(S,True,Constraint).
     * </pre>
     * @param strict
     * @param nonStrict
     * @return
     * @throws AbortionException
     */
    @Override
    public POFormula encode(Set<? extends GeneralizedRule> strict, Set<? extends GeneralizedRule> nonStrict, Abortion aborter) throws AbortionException {
        //System.out.println("S = "+strict);
        //System.out.println("N = "+nonStrict);
        // insert simplifies and tests for unsatisfiability

        ValueCache<None> knownValues = new NoValueCache<None>(this.formulaFactory);
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        args.add(this.encodeGlobalConstraints(strict, nonStrict, knownValues, null));
        args.add(this.encodeAllGreaterEqual(strict, knownValues, aborter));
        Formula<None> formula = this.formulaFactory.buildAnd(args);
        if (formula != this.ZERO) {
            args.clear();
            args.add(formula);
            args.add(this.encodeAllGreaterEqual(nonStrict, knownValues, aborter));
            formula = this.formulaFactory.buildAnd(args);
            if (formula != this.ZERO) {
                args.clear();
                args.add(formula);
                args.add(this.encodeOneGreater(strict, knownValues, aborter));
                formula = this.formulaFactory.buildAnd(args);
            }
        }
//        updating is DANGEROUS because it can remove po-constraints
//        TODO maybe add updating AFTER po-encoding
//        knownValues.update(formula);
//        formula = formula.evaluate(knownValues);
        args.clear();
        args.add(formula);
        args.add(this.encodePermutationConstraints(knownValues));
        formula = this.formulaFactory.buildAnd(args);
        POFormula poFormula = new POFormula(formula, this.factFactory.getFactMap(), this.formulaFactory, this.quasi);
        //System.out.println(poFormula);
        return poFormula;
    }

    @Override
    public POFormula encode(Set<? extends GeneralizedRule> strict, Map<? extends GeneralizedRule, QActiveCondition> activeNonStrict, boolean active, boolean allStrict, Abortion aborter) throws AbortionException {
       ValueCache<None> knownValues = new NoValueCache<None>(this.formulaFactory);
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        args.add(this.encodeGlobalConstraints(strict, activeNonStrict.keySet(), knownValues, null));
        if (allStrict) {
            args.add(this.encodeAllGreater(strict, knownValues, aborter));
        } else {
            args.add(this.encodeAllGreaterEqual(strict, knownValues, aborter));
        }
        Formula<None> formula = this.formulaFactory.buildAnd(args);
        if (formula != this.ZERO) {
            args.clear();
            args.add(formula);
            if (active) {
                args.add(this.encodeAllGreaterEqual(activeNonStrict, knownValues, aborter));
            } else {
                args.add(this.encodeAllGreaterEqual(activeNonStrict.keySet(), knownValues, aborter));
            }
            formula = this.formulaFactory.buildAnd(args);
            if (!allStrict && formula != this.ZERO) {
                args.clear();
                args.add(formula);
                args.add(this.encodeOneGreater(strict, knownValues, aborter));
                formula = this.formulaFactory.buildAnd(args);
            }
        }
        args.clear();
        args.add(formula);
        args.add(this.encodePermutationConstraints(knownValues));
        formula = this.formulaFactory.buildAnd(args);
        POFormula poFormula = new POFormula(formula, this.factFactory.getFactMap(), this.formulaFactory, this.quasi);
        return poFormula;
    }

    @Override
    public POFormula encode(Set<? extends GeneralizedRule> strict, Abortion aborter) throws AbortionException {
        ValueCache<None> knownValues = new NoValueCache<None>(this.formulaFactory);
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        args.add(this.encodeGlobalConstraints(strict, null, knownValues, null));
        args.add(this.encodeAllGreater(strict, knownValues, aborter));
        Formula<None> formula = this.formulaFactory.buildAnd(args);
//        updating is DANGEROUS because it can remove po-constraints
//        TODO maybe add updating AFTER po-encoding
//        knownValues.update(formula);
//        formula = formula.evaluate(knownValues);
        args.clear();
        args.add(formula);
        args.add(this.encodePermutationConstraints(knownValues));
        formula = this.formulaFactory.buildAnd(args);
        POFormula poFormula = new POFormula(formula, this.factFactory.getFactMap(), this.formulaFactory, this.quasi);
        //System.out.println(poFormula);
        return poFormula;
    }

    /**
     * Encode rules for RRR processors:
     * All rules have to be oriented GE, at least one must be GR.
     *
     * @param strict Set of rules
     * @param aborter Aborter
     * @return Formula with all constraints
     */
    public POFormula encodeRRR(Set<Rule> strict, Abortion aborter) throws AbortionException {
        ValueCache<None> knownValues = new NoValueCache<None>(this.formulaFactory);
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        args.add(this.encodeGlobalConstraints(strict, null, knownValues, null));
        args.add(this.encodeOneGreater(strict, knownValues, aborter));
        args.add(this.encodeAllGreaterEqual(strict, knownValues, aborter));
        Formula<None> formula = this.formulaFactory.buildAnd(args);
        args.clear();
        args.add(formula);
        args.add(this.encodePermutationConstraints(knownValues));
        formula = this.formulaFactory.buildAnd(args);
        POFormula poFormula = new POFormula(formula, this.factFactory.getFactMap(), this.formulaFactory, this.quasi);
        return poFormula;
    }

    /**
     * Encode rules for RRR processors with respect to mu-monotonicity:
     * All rules have to be oriented GE, at least one must be GR w.r.t mu.
     *
     * @param strict Set of rules
     * @param mu mu-set
     * @param aborter Aborter
     * @return Formula with all constraints
     */
    public POFormula encodeRRRMu(Set<Rule> strict, ImmutableMap<FunctionSymbol, ? extends Set<Integer>> mu, Abortion aborter) throws AbortionException {
        ValueCache<None> knownValues = new NoValueCache<None>(this.formulaFactory);
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        args.add(this.encodeGlobalConstraints(strict, null, knownValues, mu));
        args.add(this.encodeOneGreater(strict, knownValues, aborter));
        args.add(this.encodeAllGreaterEqual(strict, knownValues, aborter));
        Formula<None> formula = this.formulaFactory.buildAnd(args);
        args.clear();
        args.add(formula);
        args.add(this.encodePermutationConstraints(knownValues));
        formula = this.formulaFactory.buildAnd(args);
        POFormula poFormula = new POFormula(formula, this.factFactory.getFactMap(), this.formulaFactory, this.quasi);
        return poFormula;
    }

    /**
     * Encode rules for RRR processors with Max-SAT engine:
     * All rules have to be oriented GE, at least one must be GR.
     * All rules may be GR for Max-SAT
     *
     * @param strict Set of rules
     * @param aborter Aborter
     * @return Formula with all constraints
     */
    public Pair<POFormula, List<Formula<None>>> encodeMaxSATRRR(Set<Rule> strict, Abortion aborter) throws AbortionException {
        ValueCache<None> knownValues = new NoValueCache<None>(this.formulaFactory);
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        args.add(this.encodeGlobalConstraints(strict, null, knownValues, null));
        Pair<Formula<None>, List<Formula<None>>> maxSatPair = this.encodeOneGreaterMaxSAT(strict, knownValues, aborter);
        args.add(maxSatPair.x);
        args.add(this.encodeAllGreaterEqual(strict, knownValues, aborter));
        args.add(this.encodePermutationConstraints(knownValues));
        Formula<None> formula = this.formulaFactory.buildAnd(args);
        POFormula poFormula = new POFormula(formula, this.factFactory.getFactMap(), this.formulaFactory, this.quasi);
        return new Pair<POFormula, List<Formula<None>>>(poFormula, maxSatPair.y);
    }

    /**
     * <pre>
exists_s_lpo([],_,0).
exists_s_lpo([rule(L,R)|Rs],True,Constraint) :-
    gt_lpo(L,R,True,C1),
    (C1==1 -> C2=1 ; exists_s_lpo(Rs,True,C2)),
    simplify(C1+C2,Constraint).
     * </pre>
     * @param rules
     * @return
     * @throws AbortionException
     */
    private Formula<None> encodeOneGreater(Set<? extends GeneralizedRule> rules, ValueCache<None> knownValues, Abortion aborter) throws AbortionException {
        if (rules.size() == 1) {
            GeneralizedRule rule = rules.iterator().next();
            if (Globals.DEBUG_NOWONDER) {
                System.err.println("Encoding "+rule);
            }
            return this.encodeGR(rule.getLeft(), rule.getRight(), knownValues);
        }
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        for (GeneralizedRule rule : rules) {
            if (Globals.DEBUG_NOWONDER) {
                System.err.println("Encoding "+rule);
            }
            aborter.checkAbortion();
            Formula<None> formula = this.encodeGR(rule.getLeft(), rule.getRight(), knownValues);
            if (formula == this.ONE) {
                return formula;
            }
            args.add(formula);
        }
        return this.formulaFactory.buildOr(args);
    }

    /**
     * does the same as encodeOneGreater(), but saves the set of formulas
     * to orient GE for Max-SAT encoding.
     */
    private Pair<Formula<None>, List<Formula<None>>> encodeOneGreaterMaxSAT(Set<Rule> rules, ValueCache<None> knownValues, Abortion aborter) throws AbortionException {
        if (rules.size() == 1) {
            Rule rule = rules.iterator().next();
            if (Globals.DEBUG_NOWONDER) {
                System.err.println("Encoding "+rule);
            }
            Formula<None> form = this.encodeGR(rule.getLeft(), rule.getRight(), knownValues);
            List<Formula<None>> formlist = new ArrayList<Formula<None>>();
            formlist.add(form);
            return new Pair<Formula<None>, List<Formula<None>>>(form, formlist);
        }
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        for (Rule rule : rules) {
            if (Globals.DEBUG_NOWONDER) {
                System.err.println("Encoding "+rule);
            }
            aborter.checkAbortion();
            Formula<None> formula = this.encodeGR(rule.getLeft(), rule.getRight(), knownValues);
            if (formula == this.ONE) {
                List<Formula<None>> formlist = new ArrayList<Formula<None>>();
                formlist.add(formula);
                return new Pair<Formula<None>, List<Formula<None>>>(formula, formlist);
            }
            args.add(formula);
        }
        return new Pair<Formula<None>, List<Formula<None>>>(this.formulaFactory.buildOr(args), args);
    }


    /**
     * <pre>
forall_ns_lpo([],_,1).
forall_ns_lpo([rule(L,R)|Rs],True,Constraint) :-
    geq_lpo(L,R,True,C1),
    (C1==0 -> C2=0 ;
        update(C1,True,NewTrue),
        forall_ns_lpo(Rs,NewTrue,C2)
    ),
    simplify(C1*C2,Constraint).
     * </pre>
     * @param rules
     * @param knownValues
     * @return
     * @throws AbortionException
     */
    private Formula<None> encodeAllGreaterEqual(Set<? extends GeneralizedRule> rules, ValueCache<None> knownValues, Abortion aborter) throws AbortionException {
        if (rules.size() == 1) {
            GeneralizedRule rule = rules.iterator().next();
            if (Globals.DEBUG_NOWONDER) {
                System.err.println("Encoding "+rule);
            }
            Formula<None> formula = this.encodeGE(rule.getLeft(), rule.getRight(), knownValues);
            knownValues.update(formula);
            return formula;
        }
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        for (GeneralizedRule rule : rules) {
            if (Globals.DEBUG_NOWONDER) {
                System.err.println("Encoding "+rule);
            }
            aborter.checkAbortion();
            Formula<None> formula = this.encodeGE(rule.getLeft(), rule.getRight(), knownValues);
            if (formula == this.ZERO) {
                return formula;
            }
            knownValues.update(formula);
            args.add(formula);
        }
        return this.formulaFactory.buildAnd(args);
    }

    private Formula<None> encodeAllGreater(Set<? extends GeneralizedRule> rules, ValueCache<None> knownValues, Abortion aborter) throws AbortionException {
        if (rules.size() == 1) {
            GeneralizedRule rule = rules.iterator().next();
            if (Globals.DEBUG_NOWONDER) {
                System.err.println("Encoding "+rule);
            }
            Formula<None> formula = this.encodeGR(rule.getLeft(), rule.getRight(), knownValues);
            knownValues.update(formula);
            return formula;
        }
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        for (GeneralizedRule rule : rules) {
            if (Globals.DEBUG_NOWONDER) {
                System.err.println("Encoding "+rule);
            }
            aborter.checkAbortion();
            Formula<None> formula = this.encodeGR(rule.getLeft(), rule.getRight(), knownValues);
            if (formula == this.ZERO) {
                return formula;
            }
            knownValues.update(formula);
            args.add(formula);
        }
        return this.formulaFactory.buildAnd(args);
    }

    private Formula<None> encodeAllGreaterEqual(Map<? extends GeneralizedRule, QActiveCondition> activeRules, ValueCache<None> knownValues, Abortion aborter) throws AbortionException {
        if (activeRules.size() == 1) {
            Map.Entry<? extends GeneralizedRule, QActiveCondition> activeRule = activeRules.entrySet().iterator().next();
            GeneralizedRule rule = activeRule.getKey();
            if (Globals.DEBUG_NOWONDER) {
                System.err.println("Encoding "+rule);
            }
            QActiveCondition activeCond = activeRule.getValue();
            List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
            dArgs.add(this.encodeActiveCondition(activeCond, knownValues));
            dArgs.add(this.encodeGE(rule.getLeft(), rule.getRight(), knownValues));
            Formula<None> formula = this.formulaFactory.buildOr(dArgs);
            knownValues.update(formula);
            return formula;
        }
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        for (Map.Entry<? extends GeneralizedRule, QActiveCondition> activeRule : activeRules.entrySet()) {
            aborter.checkAbortion();
            GeneralizedRule rule = activeRule.getKey();
            if (Globals.DEBUG_NOWONDER) {
                System.err.println("Encoding "+rule);
            }
            QActiveCondition activeCond = activeRule.getValue();
            List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
            dArgs.add(this.encodeActiveCondition(activeCond, knownValues));
            dArgs.add(this.encodeGE(rule.getLeft(), rule.getRight(), knownValues));
            Formula<None> formula = this.formulaFactory.buildOr(dArgs);
            if (formula == this.ZERO) {
                return formula;
            }
            knownValues.update(formula);
            args.add(formula);
        }
        return this.formulaFactory.buildAnd(args);
    }

    private Formula<None> encodeActiveCondition(QActiveCondition activeCond, ValueCache<None> knownValues) {
        List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
        for (Set<Pair<FunctionSymbol, Integer>> poss : activeCond.getSetRepresentation()) {
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            for (Pair<FunctionSymbol, Integer> pos : poss) {
                cArgs.add(this.factFactory.getVarArg(pos.x, pos.y).evaluate(knownValues));
            }
            dArgs.add(this.formulaFactory.buildAnd(cArgs));
        }
        return this.formulaFactory.buildNot(this.formulaFactory.buildOr(dArgs));
    }

    /**
     * <pre>
geq_lpo(S,T,True,Constraint) :-
    gequals(S,T,True,C1),
    (C1==1 -> C2=1 ; gt_lpo(S,T,True,C2)),
    simplify(C1+C2, Constraint).
     * </pre>
     * @param s
     * @param t
     * @return
     */
    private Formula<None> encodeGE(TRSTerm s, TRSTerm t, ValueCache<None> knownValues) {
        Formula<None> formula = this.encodeGENGR(s,t, knownValues);
        //System.out.println(new POFormula(formula, this.factFactory.getFactMap(), this.varFactory));
        if (formula == this.ONE) {
            return formula;
        }
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        args.add(formula);
        formula = this.encodeGR(s, t, knownValues);
        //System.out.println(new POFormula(formula, this.factFactory.getFactMap(), this.varFactory));
        args.add(formula);
        return this.formulaFactory.buildOr(args);
    }

    private Formula<None> encodeEQ(TRSTerm s, TRSTerm t, ValueCache<None> knownValues) {
        Formula<None> formula = this.encodeGENGR(s,t, knownValues);
        //System.out.println(new POFormula(formula, this.factFactory.getFactMap(), this.varFactory));
        if (formula == this.ZERO) {
            return formula;
        }
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        args.add(formula);
        formula = this.encodeGENGR(t,s, knownValues);
        //System.out.println(new POFormula(formula, this.factFactory.getFactMap(), this.varFactory));
        args.add(formula);
        return this.formulaFactory.buildAnd(args);
    }

    private Formula<None> encodeNGE(TRSTerm s, TRSTerm t, ValueCache<None> knownValues) {
        return this.formulaFactory.buildNot(this.encodeGE(s,t, knownValues));
    }

    /**
     * <pre>
gequals(S,T,_,Constraint) :- var(S), var(T), !,
    (S==T -> Constraint=1 ; Constraint=0).
gequals(S,T,_, bot(F)) :- var(S),nonvar(T),T=..[F], !.


gequals(S,T,True, Constraint) :- var(S),nonvar(T),T=..[F|TArgs], !,
        evaluate(not(flag(F)),True,NotFlagF),
        (NotFlagF==0 -> C1=0;
            mysort([not(flag(F))|True],NewTrue),
            disjunction(eq,term(S),term(F,1,TArgs),NewTrue,C1)
        ),
        simplify(NotFlagF*C1,Constraint).


gequals(S,T,True,Constraint) :- nonvar(S), S=..[F|SArgs], !,
    %
    % F is noncollapsing
    evaluate(flag(F),True,FlagF),
    (FlagF==0 -> C1=0 ;
        mysort([flag(F)|True],NewTrue1),
        eq_left_noncollapsing(S,[F|SArgs],T,NewTrue1,C1)
    ),
    simplify(FlagF*C1,T1),
    %
    % F is collapsing
    (T1==1 -> T2=1 ;
        evaluate(not(flag(F)),True,NotFlagF),
        (NotFlagF==0 -> C2=0 ;
            mysort([not(flag(F))|True],NewTrue2),
            conjunction(eq,term(F,1,SArgs),term(T),NewTrue2,C2)
        ),
        simplify(NotFlagF*C2,T2)
    ),
    simplify(T1+T2,Constraint).
     * </pre>
     * @param s
     * @param t
     * @return
     */
    protected Formula<None> encodeGENGR(TRSTerm s, TRSTerm t, ValueCache<None> knownValues) {
        Triple<TRSTerm, TRSTerm, ValueCache<None>> stk = new Triple<TRSTerm, TRSTerm, ValueCache<None>>(s, t, knownValues.copy());
        Formula<None> rel = this.knownGENGR.get(stk);
        if (rel != null) {
            return rel;
        }
        Formula<None> vf = this.encodeVarConstraints(s, t, knownValues);
        if (s.isVariable()) {
            if (t.isVariable()) {
                if (s.equals(t)) {
                    return this.updateGENGR(stk, this.ONE, this.ONE);
                }
                return this.updateGENGR(stk, this.ZERO, this.ZERO);
            }
            // case s >= g(t_1, ..., t_n)=t
            TRSFunctionApplication tApp = (TRSFunctionApplication) t;
            FunctionSymbol g = tApp.getRootSymbol();
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            for (int i = 0; i < g.getArity(); i++) {
                cArgs.add(this.factFactory.getNotArg(g, i));
            }
            cArgs.add(this.factFactory.getVarFlag(g));
            Formula<None> isConstant = this.formulaFactory.buildAnd(cArgs);
            Formula<None> eIsConstant = isConstant.evaluate(knownValues);
            List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
            if (this.prec && this.xgengrc && eIsConstant != this.ZERO) {
                cArgs.clear();
                cArgs.add(this.factFactory.getVarBot(g));
                cArgs.add(eIsConstant);
                dArgs.add(this.formulaFactory.buildAnd(cArgs));
            }
            NotFormula<None> notFlagG = this.factFactory.getNotFlag(g);
            Formula<None> eNotFlagG = notFlagG.evaluate(knownValues);
            if (eNotFlagG != this.ZERO) {
                ValueCache<None> newValues = knownValues.copy();
                newValues.update(notFlagG);
                cArgs.clear();
                cArgs.add(eNotFlagG);
                cArgs.add(this.encodeDisjunction(s, tApp, OrderRelation.GENGR, newValues));
                dArgs.add(this.formulaFactory.buildAnd(cArgs));
            }
            return this.updateGENGR(stk, vf, this.formulaFactory.buildOr(dArgs));
        }
        // case s=f(t_1, ..., t_n) > t
        TRSFunctionApplication sApp = (TRSFunctionApplication) s;
        FunctionSymbol f = sApp.getRootSymbol();
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        Variable<None> varFlagF = this.factFactory.getVarFlag(f);
        Formula<None> eVarFlagF = knownValues.evaluate(varFlagF);
        if (eVarFlagF != this.ZERO && !t.isVariable()) {
            ValueCache<None> newValues = knownValues.copy();
            newValues.update(varFlagF);
            // non-collapsing f
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            cArgs.add(eVarFlagF);
            TRSFunctionApplication tApp = (TRSFunctionApplication) t;
            cArgs.add(this.encodeGENGRNonCollapsing(s, sApp, t, tApp, newValues));
            Formula<None> formula = this.formulaFactory.buildAnd(cArgs);
            if (formula == this.ONE) {
                return this.updateGENGR(stk, this.ONE, this.ONE);
            }
            args.add(formula);
        }

        // collapsing f
        NotFormula<None> notFlagF = this.factFactory.getNotFlag(f);
        Formula<None> eNotFlagF = notFlagF.evaluate(knownValues);
        if (eNotFlagF != this.ZERO) {
            ValueCache<None> newValues = knownValues.copy();
            newValues.update(notFlagF);
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            cArgs.add(eNotFlagF);
            cArgs.add(this.encodeConjunction(sApp, t, OrderRelation.GENGR, newValues));
            args.add(this.formulaFactory.buildAnd(cArgs));
        }
        return this.updateGENGR(stk, vf, this.formulaFactory.buildOr(args));
    }

    private Formula<None> updateGENGR(Triple<TRSTerm, TRSTerm, ValueCache<None>> stk, Formula<None> vf, Formula<None> formula) {
        formula = this.formulaFactory.buildAnd(vf, formula);
        this.knownGENGR.put(stk, formula);
        return formula;
    }

    /**
     * <pre>
% encoding of S>T is "0" in the following cases
%
gt_lpo(S,T,_, 0) :- S==T, !.% opt; need this case only for var(S),var(T)
gt_lpo(S,_,_, 0) :- var(S), !.


% in all other cases it worth memo-ing subresults
%
gt_lpo(W,X,Y,Z) :-
        copy_term([W,X],[A,B]),
        numbervars([A,B],1,_),
        ( lemma_gt_lpo(A,B,Y,Z) ->
            true
        ;
            gt_lpo_work(W,X,Y,Z),
            assertz(lemma_gt_lpo(A,B,Y,Z))
        ).


% encoding of S=f(...)>T  when var(T)
%        Constraint = C1+flag(F)*C2
%

gt_lpo_work(S,T,True,Constraint) :-  nonvar(S), S=..[F|SArgs], var(T), !,
        disjunction(gt,term(F,1,SArgs),term(T),True,C1),
        (C1==1 -> T2=1;
            evaluate(flag(F),True,FlagF),
            (FlagF==0 -> C2=0;
                mysort([flag(F)|True],NewTrue),
                disjunction(eq,term(F,1,SArgs),term(T),NewTrue,C2)
            ),
            simplify(FlagF*C2,T2)
        ),
        simplify(C1+T2,Constraint).

% encoding S=f(s_args)>T=g(t_args)

gt_lpo_work(S,T,True,Constraint) :-   %%% Constraint=not(flag(F))*C1 +
                                 %%%            not(flag(G))*C2 +
                                 %%%            flag(F)*flag(G)*C3
    nonvar(S), nonvar(T), S=..[F|SArgs], T=.. [G|TArgs], !,
    %
    % F is collapsing
    evaluate(not(flag(F)),True,NotFlagF),
    (NotFlagF==0 -> C1=0 ;
        mysort([not(flag(F))|True],NewTrue1),
        conjunction(gt,term(F,1,SArgs),term(T),NewTrue1,C1)
    ),
    simplify(NotFlagF*C1,T1),
    %
    % G is collapsing
    (T1==1 -> T2=1;
        evaluate(not(flag(G)),True,NotFlagG),
        (NotFlagG==0 -> C2=0 ;
            mysort([not(flag(G))|True],NewTrue2),
            conjunction(gt,term(S),term(G,1,TArgs),NewTrue2,C2)
        ),
        simplify(NotFlagG*C2,T2)
    ),
    simplify(T1+T2,Tmp),
    %
    % neither F nor G are collapsing
    (Tmp==1 -> T3=1 ;
        evaluate(flag(F),True,FlagF),
        evaluate(flag(G),True,FlagG),
        simplify(FlagF*FlagG,BothFlags),
        (BothFlags==0 -> C3=0 ;
            sort([flag(F),flag(G)|True],NewTrue3),
            gt_lpo_non_collapsing(S,[F|SArgs],T,[G|TArgs],NewTrue3,C3)
        ),
        simplify(BothFlags*C3,T3)
    ),
    simplify(Tmp+T3,Constraint).
     * </pre>
     * @param s
     * @param t
     * @return
     */
    protected Formula<None> encodeGR(TRSTerm s, TRSTerm t, ValueCache<None> knownValues) {
        Triple<TRSTerm, TRSTerm, ValueCache<None>> stk = new Triple<TRSTerm, TRSTerm, ValueCache<None>>(s,t,knownValues.copy());
        Formula<None> rel = this.knownGR.get(stk);
        if (rel != null) {
            return rel;
        }
        if (s.equals(t)) {
            return this.updateGR(stk, this.ZERO, this.ZERO);
        }
        if (s.isVariable()) {
            //this.knownRelation.put(st, Relation.NGE);
            //the above is wrong for x >= c
            return this.updateGR(stk, this.ZERO, this.ZERO);
        }
        Formula<None> vf = this.encodeVarConstraints(s, t, knownValues);
//      POFormula pf = new POFormula(vf, this.factFactory.getFactMap(), this.formulaFactory, true);
//      System.out.println(s+"\n"+t+"\n"+pf);
        TRSFunctionApplication sApp = (TRSFunctionApplication)s;
        FunctionSymbol f = sApp.getRootSymbol();
        if (t.isVariable()) {
            // case s=f(s_1, ..., s_n) > t
            List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
            Formula<None> formula = this.encodeDisjunction(sApp, t, OrderRelation.GR, knownValues);
            dArgs.add(formula);
            if (formula != this.ONE) {
                Variable<None> varFlagF = this.factFactory.getVarFlag(f);
                Formula<None> eVarFlagF = varFlagF.evaluate(knownValues);
                if (eVarFlagF != this.ZERO) {
                    ValueCache<None> newValues = knownValues.copy();
                    newValues.update(varFlagF);
                    List<Formula<None>> args = new ArrayList<Formula<None>>();
                    args.add(eVarFlagF);
                    args.add(this.encodeDisjunction(sApp, t, OrderRelation.GENGR, newValues));
                    dArgs.add(this.formulaFactory.buildAnd(args));
                }
            }
            return this.updateGR(stk, vf, this.formulaFactory.buildOr(dArgs));
        }
        // case s=f(s_1, ..., s_n) > g(t_1, ..., t_n)=t
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        NotFormula<None> notFlagF = this.factFactory.getNotFlag(f);
        Formula<None> eNotFlagF = notFlagF.evaluate(knownValues);
        if (eNotFlagF != this.ZERO) {
            // f is collapsing
            ValueCache<None> newValues = knownValues.copy();
            newValues.update(notFlagF);
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            cArgs.add(eNotFlagF);
            cArgs.add(this.encodeConjunction(sApp, t, OrderRelation.GR, newValues));
            Formula<None> formula = this.formulaFactory.buildAnd(cArgs);
            if (formula == this.ONE) {
                return this.updateGR(stk, this.ONE, this.ONE);
            }
            args.add(formula);
        }
        TRSFunctionApplication tApp = (TRSFunctionApplication) t;
        FunctionSymbol g = tApp.getRootSymbol();
        Variable<None> varFlagF = this.factFactory.getVarFlag(f);
        Formula<None> eVarFlagF = varFlagF.evaluate(knownValues);
        NotFormula<None> notFlagG = this.factFactory.getNotFlag(g);
        Formula<None> eNotFlagG = notFlagG.evaluate(knownValues);
        if (eVarFlagF != this.ZERO && eNotFlagG != this.ZERO) {
            // f is non-collapsing and g is collapsing
            ValueCache<None> newValues = knownValues.copy();
            newValues.update(varFlagF);
            newValues.update(notFlagG);
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            cArgs.add(eVarFlagF);
            cArgs.add(eNotFlagG);
            cArgs.add(this.encodeConjunction(s, tApp, OrderRelation.GR, newValues));
            Formula<None> formula = this.formulaFactory.buildAnd(cArgs);
            if (formula == this.ONE) {
                return this.updateGR(stk, this.ONE, this.ONE);
            }
            args.add(formula);
        }
        // non-collapsing f and g
        Variable<None> varFlagG = this.factFactory.getVarFlag(g);
        Formula<None> eVarFlagG = varFlagG.evaluate(knownValues);
        if (eVarFlagF != this.ZERO && eVarFlagG != this.ZERO) {
            ValueCache<None> newValues = knownValues.copy();
            newValues.update(varFlagF);
            newValues.update(varFlagG);
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            cArgs.add(eVarFlagF);
            cArgs.add(eVarFlagG);
            cArgs.add(this.encodeGRNonCollapsing(s, sApp, t, tApp, newValues));
            args.add(this.formulaFactory.buildAnd(cArgs));
        }
        return this.updateGR(stk, vf, this.formulaFactory.buildOr(args));
    }

    private Formula<None> updateGR(Triple<TRSTerm, TRSTerm, ValueCache<None>> stk, Formula<None> vf, Formula<None> formula) {
        formula = this.formulaFactory.buildAnd(vf, formula);
        this.knownGR.put(stk, formula);
        return formula;
    }

    protected Formula<None> encodeConjunction(TRSFunctionApplication sApp, TRSTerm t, OrderRelation op, ValueCache<None> knownValues) {
        List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
        FunctionSymbol f = sApp.getRootSymbol();
        int fArity = f.getArity();
        List<? extends TRSTerm> si = sApp.getArguments();
        for (int i = 0; i< fArity; i++) {
            Formula<None> formula = this.encodeConjunct(f, i, si.get(i), t, op, knownValues);
            if (formula == this.ZERO) {
                return this.ZERO;
            }
            cArgs.add(formula);
        }
        return this.formulaFactory.buildAnd(cArgs);
    }

    protected Formula<None> encodeConjunction(TRSTerm s, TRSFunctionApplication tApp, OrderRelation op, ValueCache<None> knownValues) {
        List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
        FunctionSymbol g = tApp.getRootSymbol();
        int gArity = g.getArity();
        List<? extends TRSTerm> ti = tApp.getArguments();
        for (int i = 0; i< gArity; i++) {
            Formula<None> formula = this.encodeConjunct(g, i, s, ti.get(i), op, knownValues);
            if (formula == this.ZERO) {
                return this.ZERO;
            }
            cArgs.add(formula);
        }
        return this.formulaFactory.buildAnd(cArgs);
    }

    protected Formula<None> encodeConjunction(TRSFunctionApplication sApp, TRSFunctionApplication tApp, OrderRelation op, ValueCache<None> knownValues) {
        List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
        FunctionSymbol f = sApp.getRootSymbol();
        if (Globals.useAssertions) {
            assert f.equals(tApp.getRootSymbol());
        }
        int fArity = f.getArity();
        List<? extends TRSTerm> si = sApp.getArguments();
        List<? extends TRSTerm> ti = tApp.getArguments();
        for (int i = 0; i< fArity; i++) {
            Formula<None> formula = this.encodeConjunct(f, i, si.get(i), ti.get(i), op, knownValues);
            if (formula == this.ZERO) {
                return this.ZERO;
            }
            cArgs.add(formula);
        }
        return this.formulaFactory.buildAnd(cArgs);
    }

    protected Formula<None> encodeConjunct(FunctionSymbol f, int i, TRSTerm s, TRSTerm t, OrderRelation op, ValueCache<None> knownValues) {
        NotFormula<None> notFArgI = this.factFactory.getNotArg(f, i);
        Formula<None> eNotFArgI = notFArgI.evaluate(knownValues);
        if (eNotFArgI == this.ONE) {
            return this.ONE;
        }
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        args.add(eNotFArgI);
        ValueCache<None> newValues = knownValues.copy();
        Variable<None> varFArgI = this.factFactory.getVarArg(f, i);
        newValues.update(varFArgI);
        switch (op) {
        case GR:
            args.add(this.encodeGR(s, t, newValues));
            break;
        case GE:
            args.add(this.encodeGE(s, t, newValues));
            break;
        case GENGR:
            args.add(this.encodeGENGR(s, t, newValues));
            break;
        default:
            throw new RuntimeException("I only know GR, GE, and GENGR");
        }
        return this.formulaFactory.buildOr(args);
    }

    protected Formula<None> encodeDisjunction(TRSFunctionApplication sApp, TRSTerm t, OrderRelation op, ValueCache<None> knownValues) {
        List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
        FunctionSymbol f = sApp.getRootSymbol();
        int fArity = f.getArity();
        List<? extends TRSTerm> si = sApp.getArguments();
        for (int i = 0; i< fArity; i++) {
            Formula<None> formula = this.encodeDisjunct(f, i, si.get(i), t, op, knownValues);
            if (formula == this.ONE) {
                return this.ONE;
            }
            dArgs.add(formula);
        }
        return this.formulaFactory.buildOr(dArgs);
    }

    protected Formula<None> encodeDisjunction(TRSTerm s, TRSFunctionApplication tApp, OrderRelation op, ValueCache<None> knownValues) {
        List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
        FunctionSymbol g = tApp.getRootSymbol();
        int gArity = g.getArity();
        List<? extends TRSTerm> ti = tApp.getArguments();
        for (int i = 0; i< gArity; i++) {
            Formula<None> formula = this.encodeDisjunct(g, i, s, ti.get(i), op, knownValues);
            if (formula == this.ONE) {
                return this.ONE;
            }
            dArgs.add(formula);
        }
        return this.formulaFactory.buildOr(dArgs);
    }

    private Formula<None> encodeDisjunct(FunctionSymbol f, int i, TRSTerm s, TRSTerm t, OrderRelation op, ValueCache<None> knownValues) {
        Variable<None> varFArgI = this.factFactory.getVarArg(f, i);
        Formula<None> eVarFArgI = varFArgI.evaluate(knownValues);
        if (eVarFArgI == this.ZERO) {
            return this.ZERO;
        }
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        args.add(eVarFArgI);
        ValueCache<None> newValues = knownValues.copy();
        newValues.update(varFArgI);
        switch (op) {
        case GR:
            args.add(this.encodeGR(s, t, newValues));
            break;
        case GE:
            args.add(this.encodeGE(s, t, newValues));
            break;
        case GENGR:
            args.add(this.encodeGENGR(s, t, newValues));
            break;
        default:
            throw new RuntimeException("I only know GR, GE, and GENGR");
        }
        return this.formulaFactory.buildAnd(args);
    }

    /**
     * <pre>
global(S,N,True,Constraint) :-
        alphabet(S,N,Symbols),
        conjunction_on_symbols(Symbols,Constraint),
        update(Constraint,[],True).

alphabet(S,N,Symbols) :-
        findall(F/I,((member(rule(L,R),S);member(rule(L,R),N)),
                     (T=L;T=R),functorIN(T,F/I)),  List),
        sort(List,Symbols).

functorIN(Term,F/N) :-
    nonvar(Term), functor(Term,F,N).
functorIN(Term,F/N) :-
    nonvar(Term), Term=..[_|Args], member(Arg,Args), functorIN(Arg,F/N).

conjunction_on_symbols([],1) :- !.
conjunction_on_symbols([F/N|Ss],Constraint) :-
    foreach_symbol(F/N,C1),
    conjunction_on_symbols(Ss,C2),
    simplify(C1*C2,Constraint).

foreach_symbol(F/0,flag(F)) :- !.
foreach_symbol(F/N,Constraint) :-
    findall(F/I,between(1,N,I),FIs),
    findall(Conjunction,one_is_true(FIs,Conjunction),List),
    list2disj(List,Disj),
    simplify(flag(F)+Disj,Constraint).

list2disj([],0) :- !.
list2disj([X],X) :- !.
list2disj([X,Y|Xs], X+Conj) :- !, list2disj([Y|Xs],Conj).
     * </pre>
     * @param strict
     * @param nonStrict
     * @param knownValues
     * @return
     */
    public Formula<None> encodeGlobalConstraints(Set<? extends GeneralizedRule> strict, Set<? extends GeneralizedRule> nonStrict, ValueCache<None> knownValues, final ImmutableMap<FunctionSymbol, ? extends Set<Integer>> mu) {
        Set<FunctionSymbol> sig = aprove.verification.dpframework.BasicStructures.CollectionUtils.getFunctionSymbols(strict);
        if (nonStrict != null) {
            sig.addAll(aprove.verification.dpframework.BasicStructures.CollectionUtils.getFunctionSymbols(nonStrict));
        }
        return this.encodeGlobalConstraints(sig, knownValues, mu);
    }
    public Formula<None> encodeGlobalConstraints(Set<FunctionSymbol> sig, ValueCache<None> knownValues, final ImmutableMap<FunctionSymbol, ? extends Set<Integer>> mu) {
        this.sig = sig;
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        for (FunctionSymbol f : sig) {
            int arity = f.getArity();
            Set<Integer> intSet = null;
            if (mu != null)  {
                intSet = mu.get(f);
            }
            // Prevent null-pointer exceptions
            if (intSet == null) {
                intSet = new LinkedHashSet<Integer>(arity);
                for (int i = 0; i < arity; i++) {
                    intSet.add(i);
                }
            }
            if (Globals.DEBUG_NOWONDER) {
                System.err.println("Encoding "+f);
            }
            switch (this.afstype) {
            case MONOTONEAFS:
                if (arity == 1) {
                    // If mu is defined, respect it
                    // In any other case, the argument must be monotone
                    if (mu == null || intSet.contains(Integer.valueOf(0))) {
                        args.add(this.factFactory.getVarArg(f, 0));
                    } else {
                        List<Formula<None>> dArgs = new ArrayList<Formula<None>>(2);
                        dArgs.add(this.factFactory.getVarArg(f, 0));
                        dArgs.add(this.factFactory.getVarFlag(f));
                        args.add(this.formulaFactory.buildOr(dArgs));
                    }
                } else {
                    args.add(this.factFactory.getVarFlag(f));
                    if (mu == null) {
                        for (int i = 0; i < arity; i++) {
                            args.add(this.factFactory.getVarArg(f, i));
                        }
                    } else {
                        // Encode mu-monotonicity
                        for (Integer i : intSet) {
                            args.add(this.factFactory.getVarArg(f, i));
                        }
                    }
                }
                break;
            case NOAFS:
            args.add(this.factFactory.getVarFlag(f));
            for (int i = 0; i < arity; i++) {
                args.add(this.factFactory.getVarArg(f, i));
            }
            break;
            case FULLAFS:
                if (arity == 0) {
                    Variable<None> var = this.factFactory.getVarFlag(f);
                    args.add(var);
                } else {
                    List<Formula<None>> dArgs = new ArrayList<Formula<None>>(2);
                    if (this.restriction > 0 && this.restriction < arity) {
                        List<Formula<None>> cArgs = new ArrayList<Formula<None>>(2);
                        cArgs.add(this.factFactory.getVarFlag(f));
                        cArgs.add(this.encodeRestriction(f, this.restriction));
                        dArgs.add(this.formulaFactory.buildAnd(cArgs));
                    } else {
                        dArgs.add(this.factFactory.getVarFlag(f));
                    }
                    dArgs.add(this.patterns.encodeExactlyOne(this.factFactory.getVarArgs(f)));
                    args.add(this.formulaFactory.buildOr(dArgs));
                }
                break;
            }
            if (Options.certifier.isA3pat() && this.lex) {
                for (int i = 0; i < arity; i++) {
                    List<Formula<None>> dArgs = new ArrayList<Formula<None>>(arity+1);
                    dArgs.add(this.factFactory.getNotArg(f, i));
                    for (int k = 0; k < arity; k++) {
                        dArgs.add(this.factFactory.getVarPerm(f, i, k));
                    }
                    args.add(this.formulaFactory.buildOr(dArgs));
                }
                for (FunctionSymbol g : sig) {
                    if (f.equals(g)) {
                        continue;
                    }
                    List<Formula<None>> aArgs = new ArrayList<Formula<None>>();
                    int gArity = g.getArity();
                    for (int k = 0; k < arity; k++) {
                        for (int i = 0; i < arity; i++) {
                            List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
                            Formula<None> notFPermIK = this.factFactory.getNotPerm(f, i, k);
                            Formula<None> eNotFPermIK = notFPermIK.evaluate(knownValues);
                            dArgs.add(eNotFPermIK);
                            if (eNotFPermIK != this.ONE) {
                                NotFormula<None> notFArgI = this.factFactory.getNotArg(f, i);
                                Formula<None> eNotFArgI = notFArgI.evaluate(knownValues);
                                dArgs.add(eNotFArgI);
                                if (eNotFArgI != this.ONE && k < gArity) {
                                    for (int j = 0; j < gArity; j++) {
                                        List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
                                        Formula<None> varGPermJK = this.factFactory.getVarPerm(g, j, k);
                                        Formula<None> eVarGPermJK = varGPermJK.evaluate(knownValues);
                                        cArgs.add(eVarGPermJK);
                                        if (eVarGPermJK != this.ZERO) {
                                            Variable<None> varGArgJ = this.factFactory.getVarArg(g, j);
                                            Formula<None> eVarGArgJ = varGArgJ.evaluate(knownValues);
                                            cArgs.add(eVarGArgJ);
                                        }
                                        dArgs.add(this.formulaFactory.buildAnd(cArgs));
                                    }
                                }
                            }
                            aArgs.add(this.formulaFactory.buildOr(dArgs));
                        }
/*                        for (int j = 0; j < gArity; j++) {
                            List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
                            Formula<None> notGPermJK = this.factFactory.getNotPerm(g, j, k);
                            Formula<None> eNotGPermJK = notGPermJK.evaluate(knownValues);
                            dArgs.add(eNotGPermJK);
                            if (eNotGPermJK != this.ONE) {
                                NotFormula<None> notGArgJ = this.factFactory.getNotArg(g, j);
                                Formula<None> eNotGArgJ = notGArgJ.evaluate(knownValues);
                                dArgs.add(eNotGArgJ);
                                if (eNotGArgJ != this.ONE) {
                                    for (int i = 0; i < arity; i++) {
                                        List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
                                        Formula<None> varFPermIK = this.factFactory.getVarPerm(f, i, k);
                                        Formula<None> eVarFPermIK = varFPermIK.evaluate(knownValues);
                                        cArgs.add(eVarFPermIK);
                                        if (eVarFPermIK != this.ZERO) {
                                            Variable<None> varFArgI = this.factFactory.getVarArg(f, i);
                                            Formula<None> eVarFArgI = varFArgI.evaluate(knownValues);
                                            cArgs.add(eVarFArgI);
                                        }
                                        dArgs.add(this.formulaFactory.buildAnd(cArgs));
                                    }
                                }
                            }
                            aArgs.add(this.formulaFactory.buildOr(dArgs));
                        }*/
                    }
                    args.add(this.formulaFactory.buildOr(this.factFactory.getNotEqual(f, g), this.formulaFactory.buildAnd(aArgs)));
                }
            }
        }
        Formula<None> formula = this.formulaFactory.buildAnd(args);
        knownValues.update(formula);
        return formula;
    }

    @Override
    public Afs getAfs(Set<Variable<None>> knownTrue) {
        Afs afs = new Afs();
        for (FunctionSymbol f : this.sig) {
            int arity = f.getArity();
            Variable[] varArgs = this.factFactory.getVarArgs(f);
            if (knownTrue.contains(this.factFactory.getVarFlag(f))) {
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

    @Override
    public abstract AfsOrder getOrder(Set<Variable<None>> knownTrue, Afs afs);

    public Formula<None> encodeRestriction(FunctionSymbol f, int restriction) {
        RestrictionEncoder re = new RestrictionEncoder(this.formulaFactory);
        Variable<None>[] vars = this.factFactory.getVarArgs(f);
        NotFormula<None>[] nots = this.factFactory.getNotArgs(f);
        return re.encodeRestriction(vars, nots, restriction);
    }

    public class RestrictionEncoder {

        private Variable<None>[] vars;
        private NotFormula<None>[] nots;
        private Stack<Boolean> stack;
        private List<Formula<None>> list;
        private int restriction;
        private FormulaFactory<None> formulaFactory;

        public RestrictionEncoder(FormulaFactory<None> formulaFactory) {
            this.formulaFactory = formulaFactory;
        }

        public Formula<None> encodeRestriction(Variable<None>[] vars, NotFormula<None>[] nots, int restriction) {
            this.list = new ArrayList<Formula<None>>();
            this.stack = new Stack<Boolean>();
            this.vars = vars;
            this.nots = nots;
            this.restriction = restriction;
            this.encode(0, 0);
            return this.formulaFactory.buildAnd(this.list);
        }

        private void encode(int i, int selected) {
            if (i == this.vars.length) {
                List<Formula<None>> left = new ArrayList<Formula<None>>();
                List<Formula<None>> right = new ArrayList<Formula<None>>();
                for (int j = 0; j < i; j++) {
                    if (this.stack.get(j) == Boolean.TRUE) {
                        left.add(this.vars[j]);
                    } else {
                        right.add(this.nots[j]);
                    }
                }
                List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
                dArgs.add(this.formulaFactory.buildNot(this.formulaFactory.buildAnd(left)));
                dArgs.add(this.formulaFactory.buildAnd(right));
                this.list.add(this.formulaFactory.buildOr(dArgs));
            } else {
                if (selected < this.restriction) {
                    this.stack.push(Boolean.TRUE);
                    this.encode(i+1, selected+1);
                    this.stack.pop();
                }
                if (i-selected < this.vars.length-this.restriction) {
                    this.stack.push(Boolean.FALSE);
                    this.encode(i+1, selected);
                    this.stack.pop();
                }
            }
        }

    }

    @Override
    public boolean isAllowQuasi() {
        return this.quasi;
    }

    public Formula<None> encodeVarConstraints(TRSTerm s, TRSTerm t,  ValueCache<None> knownValues) {
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        Map<aprove.verification.dpframework.BasicStructures.TRSVariable, List<List<Formula<None>>>> sMap = this.getVarMap(s);
        Map<aprove.verification.dpframework.BasicStructures.TRSVariable, List<List<Formula<None>>>> tMap = this.getVarMap(t);
        for (Map.Entry<aprove.verification.dpframework.BasicStructures.TRSVariable, List<List<Formula<None>>>> entry : tMap.entrySet()) {
            aprove.verification.dpframework.BasicStructures.TRSVariable tVar = entry.getKey();
            List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            for (List<Formula<None>> pos : entry.getValue()) {
                cArgs.add(this.formulaFactory.buildNot(this.formulaFactory.buildAnd(pos)));
            }
            dArgs.add(this.formulaFactory.buildAnd(cArgs));
            List<List<Formula<None>>> sPoss = sMap.get(tVar);
            if (sPoss != null) {
                for (List<Formula<None>> pos : sPoss) {
                    dArgs.add(this.formulaFactory.buildAnd(pos));
                }
            }
            args.add(this.formulaFactory.buildOr(dArgs));
        }
        return this.formulaFactory.buildAnd(args).evaluate(knownValues);
    }

    private Map<aprove.verification.dpframework.BasicStructures.TRSVariable, List<List<Formula<None>>>> getVarMap(TRSTerm t) {
        Map<aprove.verification.dpframework.BasicStructures.TRSVariable, List<List<Formula<None>>>> map = new LinkedHashMap<aprove.verification.dpframework.BasicStructures.TRSVariable, List<List<Formula<None>>>>();
        List<Formula<None>> pos = new ArrayList<Formula<None>>();
        this.getVarMap(t, map, pos);
        return map;
    }

    private void getVarMap(TRSTerm t, Map<aprove.verification.dpframework.BasicStructures.TRSVariable, List<List<Formula<None>>>> map, List<Formula<None>> pos) {
        if (t.isVariable()) {
            aprove.verification.dpframework.BasicStructures.TRSVariable var = (aprove.verification.dpframework.BasicStructures.TRSVariable) t;
            List<List<Formula<None>>> poss = map.get(var);
            if (poss == null) {
                poss = new ArrayList<List<Formula<None>>>();
                map.put(var, poss);
            }
            poss.add(new ArrayList<Formula<None>>(pos));
        } else {
            TRSFunctionApplication fApp = (TRSFunctionApplication) t;
            List<? extends TRSTerm> args = fApp.getArguments();
            FunctionSymbol f = fApp.getRootSymbol();
            int arity = f.getArity();
            if (Globals.useAssertions) {
                assert(arity == args.size());
            }
            Variable<None>[] varArgs = this.factFactory.getVarArgs(f);
            for (int i = 0; i < arity; i++) {
                pos.add(varArgs[i]);
                this.getVarMap(args.get(i), map, pos);
                pos.remove(pos.size()-1);
            }
        }
    }

    @Override
    public QActiveOrder decode(int[] satModel, Abortion aborter)
            throws AbortionException {
        Set<Variable<None>> knownTrue = this.poFormula.decode(satModel, this.formula.getId());
        Afs afs = this.getAfs(knownTrue);
        QActiveOrder order = this.getOrder(knownTrue, afs);
        return order;
    }

    @Override
    public Formula<None> encode(Constraint<TRSTerm> c, Abortion aborter)
            throws AbortionException {
        ValueCache<None> knownValues = new NoValueCache<None>(this.formulaFactory);
        TRSTerm left = c.getLeft();
        TRSTerm right = c.getRight();
        switch (c.getType()) {
        case GE:
            return this.encodeGE(left, right, knownValues);
        case GENGR:
            return this.encodeGENGR(left, right, knownValues);
        case GR:
            return this.encodeGR(left, right, knownValues);
        case EQ:
            return this.encodeEQ(left, right, knownValues);
        case NGE:
            return this.encodeNGE(left, right, knownValues);
        default:
            return this.ONE;
        }
    }

    @Override
    public Formula<None> encodeQActiveAtom(FunctionSymbol f, int i, Abortion aborter) throws AbortionException {
        return this.factFactory.getVarArg(f, i);
    }

    @Override
    public FormulaFactory<None> getFormulaFactory() {
        return this.formulaFactory;
    }

    @Override
    public Formula<None> post(Abortion aborter) throws AbortionException {
        ValueCache<None> knownValues = new NoValueCache<None>(this.formulaFactory);
        return this.encodePermutationConstraints(knownValues);
    }

    @Override
    public Formula<None> pre(Set<FunctionSymbol> sig,
            Abortion aborter) throws AbortionException {
        ValueCache<None> knownValues = new NoValueCache<None>(this.formulaFactory);
        return this.encodeGlobalConstraints(sig, knownValues, null);
    }

    @Override
    public Formula<None> toFinalFormula(Formula<None> f, Abortion aborter)
            throws AbortionException {
        this.poFormula = new POFormula(f, this.factFactory.getFactMap(), this.formulaFactory, this.quasi);
        PLEncoder plEncoder = new SimpleBinaryPLEncoder(this.formulaFactory, this.quasi);
        this.formula = plEncoder.toPropositionalFormula(this.poFormula, aborter);
        return this.formula;
    }

    @Override
    public POFormula encode(Map<Rule, QActiveCondition> usableRules, Afs initialAfs, Abortion aborter) throws AbortionException {
        ValueCache<None> knownValues = new NoValueCache<None>(this.formulaFactory);
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        Set<FunctionSymbol> sig = aprove.verification.dpframework.BasicStructures.CollectionUtils.getFunctionSymbols(usableRules.keySet());
        sig.addAll(initialAfs.getFunctionSymbols());
        args.add(this.encodeGlobalConstraints(sig, knownValues, null));
        args.add(this.encodeInitialAfs(initialAfs));
        args.add(this.encodeAllGreaterEqual(usableRules, knownValues, aborter));
        args.add(this.encodePermutationConstraints(knownValues));
        Formula<None> formula = this.formulaFactory.buildAnd(args);
        POFormula poFormula = new POFormula(formula, this.factFactory.getFactMap(), this.formulaFactory, this.quasi);
        return poFormula;
    }

    private Formula<None> encodeInitialAfs(Afs initialAfs) {
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        for (Triple<FunctionSymbol, YNM[], Boolean> filter : initialAfs.getFilterings()) {
            FunctionSymbol f = filter.x;
            YNM[] regarded = filter.y;
            boolean collapse = filter.z;
            if (collapse) {
                args.add(this.factFactory.getNotFlag(f));
            } else {
                args.add(this.factFactory.getVarFlag(f));
            }
            int arity = f.getArity();
            for (int i = 0; i < arity; i++) {
                Variable<None>[] varArgs = this.factFactory.getVarArgs(f);
                NotFormula<None>[] notArgs = this.factFactory.getNotArgs(f);
                switch (regarded[i]) {
                case YES:
                    args.add(varArgs[i]);
                    break;
                case NO:
                    args.add(notArgs[i]);
                    break;
                default:
                    assert(false);
                }
            }
        }
        return this.formulaFactory.buildAnd(args);
    }

}
