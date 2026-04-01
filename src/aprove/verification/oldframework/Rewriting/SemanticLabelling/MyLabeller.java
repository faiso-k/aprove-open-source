package aprove.verification.oldframework.Rewriting.SemanticLabelling;

import java.util.*;
import java.util.Map.Entry;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.MaxMinPolynomials.*;
import aprove.verification.dpframework.TRSProblem.Processors.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class MyLabeller {

    private final Set<Rule> oldRules;
    private final Set<String> usedNames;
    private MyModel actualModel;
    private final Map<TRSFunctionApplication, TRSFunctionApplication> termMap;
    private Map<Rule, Rule> labRuleToOriginRule = new HashMap<Rule, Rule>();
    private Map<TRSFunctionApplication, TRSFunctionApplication> labQTermToOriginQTerm =
        new HashMap<TRSFunctionApplication, TRSFunctionApplication>();
    private final Set<FunctionSymbol> signature;
    private Map<String, String> variableRenaming;
    private ArrayList<TRSTerm> succContainer = new ArrayList<TRSTerm>(1);
    private final FreshNameGenerator freshGen;
    private final FreshNameGenerator variableFreshGen;
    private final TRSVariable varX;
    private final TRSVariable varY;
    private final FunctionSymbol SUC;
    private final FunctionSymbol PLUS;
    private final FunctionSymbol TIMES;
    private final FunctionSymbol MIN;
    private final FunctionSymbol MAX;
    private final TRSTerm ZERO;
    private final TRSTerm ONE;

    public MyLabeller(Set<Rule> originalRules,
        Map<TRSFunctionApplication, TRSFunctionApplication> oldToTransformedTerm) {
        this.oldRules = originalRules;
        this.termMap = oldToTransformedTerm;
        this.signature = MyLabeller.calculateSignature(this.oldRules, new LinkedHashSet<FunctionSymbol>());
        this.usedNames = MyLabeller.getUsedNames(this.oldRules, this.signature, new HashSet<String>());
        this.freshGen = new FreshNameGenerator(this.usedNames, FreshNameGenerator.VARIABLES);
        this.variableFreshGen = new FreshNameGenerator(this.usedNames, FreshNameGenerator.SEMLAB_VARS);
        this.varX = TRSTerm.createVariable(this.freshGen.getFreshName("x", true));
        this.varY = TRSTerm.createVariable(this.freshGen.getFreshName("y", true));
        this.SUC = FunctionSymbol.create(this.freshGen.getFreshName("labS", true), 1);
        this.PLUS = FunctionSymbol.create(this.freshGen.getFreshName("labPlus", true), 2);
        this.TIMES = FunctionSymbol.create(this.freshGen.getFreshName("labTimes", true), 2);
        this.MIN = FunctionSymbol.create(this.freshGen.getFreshName("labMin", true), 2);
        this.MAX = FunctionSymbol.create(this.freshGen.getFreshName("labMax", true), 2);
        this.ZERO = TRSTerm.createFunctionApplication(
            FunctionSymbol.create(this.freshGen.getFreshName("labZ", true), 0),
            ImmutableCreator.create(new ArrayList<TRSTerm>()));
        this.ONE = MyLabeller.myCreate(this.ZERO, this.SUC);
        this.variableRenaming = new HashMap<String, String>();
        this.succContainer.add(null);

    }

    private static TRSTerm myCreate(TRSTerm zero, FunctionSymbol suc) {
        ArrayList<TRSTerm> al = new ArrayList<TRSTerm>(1);
        al.add(zero);
        return TRSTerm.createFunctionApplication(
            suc,
            ImmutableCreator.create(al));
    }

    private static TRSTerm createSuc(TRSVariable var, FunctionSymbol suc) {
        ArrayList<TRSTerm> args = new ArrayList<TRSTerm>(1);
        args.add(var);
        TRSFunctionApplication sucVar =
            TRSTerm.createFunctionApplication(
                suc,
                ImmutableCreator.create(args));
        return sucVar;
    }

    private static LinkedHashSet<FunctionSymbol> calculateSignature(
        Collection<Rule> rules,
        LinkedHashSet<FunctionSymbol> signature) {
        for (Rule r : rules) {
            signature.addAll(r.getFunctionSymbols());
        }
        return signature;
    }

    private static Set<String> getUsedNames(Set<Rule> rules, Set<FunctionSymbol> fSyms, Set<String> names) {
        for (FunctionSymbol fSym : fSyms) {
            names.add(fSym.getName());
        }
        Set<TRSVariable> vars;
        for (Rule r : rules) {
            vars = r.getVariables();
            for (TRSVariable v : vars) {
                names.add(v.getName());
            }
        }
        return names;
    }

    public LinkedHashSet<Rule> unlabelRules(Collection<Rule> labRules) {
        LinkedHashSet<Rule> rules = new LinkedHashSet<Rule>();
        for (Rule r : labRules) {
            Rule oldRule = this.labRuleToOriginRule.get(r);
            if (Globals.useAssertions) {
                assert (oldRule != null) : "MyLabbeller: unlabelRules: SemLab was invoked with rule changing strategy!";
            }
            rules.add(oldRule);
        }
        return rules;
    }

    public LinkedHashSet<Rule> labelRules(MyModel model) {
        LinkedHashSet<Rule> labelledRules = new LinkedHashSet<Rule>();
        this.actualModel = model;
        this.labRuleToOriginRule.clear();
        for (Rule r : this.oldRules) {
            this.variableFreshGen.setUsedToOrigin();
            this.variableRenaming.clear();
            TRSFunctionApplication newLhs = null;
            Pair<TRSTerm, TRSTerm> labLhs = this.processTermOfLhs(r.getLeft(), true);
            if (labLhs == null) {
                labelledRules.clear();
                break;
            }
            else {
                newLhs = (TRSFunctionApplication)labLhs.y;
            }
            Pair<TRSTerm, TRSTerm> labRhs = this.processTermOfLhs(r.getRight(), true);
            TRSTerm newRhs = null;
            if (labRhs == null) {
                newRhs = this.processTermOfRhs(r.getRight()).y;
            }
            else {
                newRhs = labRhs.y;
            }
            Rule labRule = Rule.create(newLhs, newRhs);
            labelledRules.add(labRule);
            this.labRuleToOriginRule.put(labRule, r);
        }
        return labelledRules;
    }

    /**
     * This method labels qterms in full arbitrary labelling.<br>
     * Arbitrary as in the dissertation of Thiemann, the Q underbar.
     * @param qterms
     * @return
     */
    public Set<TRSFunctionApplication> labelQTerms(Collection<TRSFunctionApplication> qterms) {
        Set<TRSFunctionApplication> labTerms = new HashSet<TRSFunctionApplication>(qterms.size());
        this.labQTermToOriginQTerm.clear();
        for (TRSFunctionApplication t : qterms) {
            this.variableFreshGen.setUsedToOrigin();
            TRSFunctionApplication labTerm = (TRSFunctionApplication)this.labelTerm(t).y;
            labTerms.add(labTerm);
        }
        return labTerms;
    }

    public Set<TRSFunctionApplication> unlabelQTerms(Collection<TRSFunctionApplication> labTerms) {
        if (Globals.useAssertions) {
            for (TRSTerm t : labTerms) {
                assert (this.labQTermToOriginQTerm.get(t) != null) : "MyLabbeller: unlabelTerms: SemLab was invoked with qterms changing strategy!";
            }
        }
        return this.labQTermToOriginQTerm.keySet();
    }

    /**
     * NOTE: This method is only to label qterms in full arbitrary labelling.<br>
     * Arbitrary as in the dissertation of Thiemann, the Q underbar.
     * @param t
     * @return
     */
    private Pair<TRSTerm, TRSTerm> labelTerm(TRSTerm t) {
        Pair<TRSTerm, TRSTerm> result;
        if (t.isVariable()) {
            TRSVariable v = (TRSVariable)t;
            String newName = this.variableFreshGen.getFreshName(v.getName(), false);
            result = new Pair<TRSTerm, TRSTerm>(TRSTerm.createVariable(newName), t);
        }
        else {
            TRSFunctionApplication fApp = (TRSFunctionApplication)t;
            FunctionSymbol root = fApp.getRootSymbol();
            int arity = root.getArity();
            String newName = this.variableFreshGen.getFreshName(root.getName(), false);
            if (arity == 0) {
                result = new Pair<TRSTerm, TRSTerm>(TRSTerm.createVariable(newName), t);
            }
            else {
                ArrayList<TRSTerm> labArgs = new ArrayList<TRSTerm>(2 * arity);
                ArrayList<TRSTerm> oldArgs = new ArrayList<TRSTerm>(arity);
                for (int i = 0; i < arity; i++) {
                    Pair<TRSTerm, TRSTerm> dummy = this.labelTerm(fApp.getArgument(i));
                    labArgs.add(i, dummy.x);
                    oldArgs.add(dummy.y);
                }
                labArgs.addAll(oldArgs);
                FunctionSymbol labF = FunctionSymbol.create(root.getName(), 2 * arity);
                TRSFunctionApplication labFapp =
                    TRSTerm.createFunctionApplication(labF, ImmutableCreator.create(labArgs));
                result = new Pair<TRSTerm, TRSTerm>(TRSTerm.createVariable(newName), labFapp);
            }
        }
        return result;
    }

    private Pair<TRSTerm, TRSTerm> processTermOfLhs(TRSTerm t, boolean onTop) {
        Pair<TRSTerm, TRSTerm> result;
        boolean rewritePlus = false;
        if (t.isVariable()) {
            TRSVariable v = (TRSVariable)t;
            String newName = this.variableRenaming.get(v.getName());
            if (newName == null) {
                newName = this.variableFreshGen.getFreshName(v.getName(), false);
                this.variableRenaming.put(v.getName(), newName);
            }
            result = new Pair<TRSTerm, TRSTerm>(TRSTerm.createVariable(newName), t);
        }
        else {
            Map<String, VarPolynomial> varRenaming = new HashMap<String, VarPolynomial>();
            TRSFunctionApplication fApp = (TRSFunctionApplication)t;
            Set<TRSVariable> vars = fApp.getVariables();
            for (TRSVariable v : vars) {
                String newName = this.variableRenaming.get(v.getName());
                if (newName == null) {
                    newName = this.variableFreshGen.getFreshName(v.getName(), false);
                    this.variableRenaming.put(v.getName(), newName);
                }
                varRenaming.put(v.getName(), VarPolynomial.createVariable(newName));
            }
            FunctionSymbol fSym = fApp.getRootSymbol();
            int arity = fSym.getArity();
            if (arity == 0) {
                MaxMinPolynomial labMMP = this.actualModel.calculateMMpolyOfTermWithVarRenaming(t, varRenaming);
                TRSTerm label = this.transformMMP(labMMP);
                result = new Pair<TRSTerm, TRSTerm>(label, fApp);
            } else {
                ImmutableList<? extends TRSTerm> args = fApp.getArguments();
                int position = 0;
                ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>((2 * arity));
                for (int i = 0; i < (2 * arity); i++) {
                    newArgs.add(null);
                }
                for (TRSTerm arg : args) {
                    Pair<TRSTerm, TRSTerm> pair = this.processTermOfLhs(arg, false);
                    if (pair == null) {
                        return null;
                    }
                    newArgs.set(position, pair.x);
                    newArgs.set((position + arity), pair.y);
                    position++;
                }
                TRSFunctionApplication labfApp =
                    TRSTerm.createFunctionApplication(
                        FunctionSymbol.create(fSym.getName(), (2 * arity)),
                        ImmutableCreator.create(newArgs));
                MaxMinPolynomial labMMP;
                if (arity > 2) {
                    TRSTerm tTrans = this.termMap.get(t);
                    labMMP = this.actualModel.calculateMMpolyOfTermWithVarRenaming(tTrans, varRenaming);
                }
                else {
                    labMMP = this.actualModel.calculateMMpolyOfTermWithVarRenaming(t, varRenaming);
                }
                //Check if the actual label is valid, e.g. it is only allowed to be a Constant, Variable or Variable plus Constant
                if (!onTop) {
                    MMPolyMetaInf mInf = labMMP.getMetaInf();
                    if (mInf != MMPolyMetaInf.Constant) {
                        if (mInf != MMPolyMetaInf.VarPoly) {
                            return null;
                        }
                        else {
                            VarPolynomial vp = labMMP.getVarPolynomial();
                            ImmutableMap<IndefinitePart, SimplePolynomial> monomials = vp.getVarMonomials();
                            if (monomials.size() > 2) {
                                return null;
                            }
                            else {
                                if (monomials.size() == 2) {
                                    Iterator<Entry<IndefinitePart, SimplePolynomial>> iter =
                                        monomials.entrySet().iterator();
                                    while (iter.hasNext()) {
                                        Entry<IndefinitePart, SimplePolynomial> entry = iter.next();
                                        IndefinitePart ip = entry.getKey();
                                        if (!ip.isIndefinite()) {
                                            if (!ip.isEmpty()) {
                                                return null;
                                            }
                                            else {
                                                if (!entry.getValue().isConstant()) {
                                                    return null;
                                                }
                                                else {
                                                    rewritePlus = true;
                                                }
                                            }
                                        }
                                        else {
                                            if (!entry.getValue().isConstant()) {
                                                return null;
                                            }
                                            else {
                                                rewritePlus = true;
                                            }
                                        }
                                    }
                                }
                                else {
                                    Entry<IndefinitePart, SimplePolynomial> entry =
                                        monomials.entrySet().iterator().next();
                                    IndefinitePart ip = entry.getKey();
                                    if (!ip.isIndefinite()) {
                                        if (!ip.isEmpty()) {
                                            return null;
                                        }
                                        else {
                                            if (!entry.getValue().isConstant()) {
                                                return null;
                                            }
                                        }
                                    }
                                    else {
                                        if (!entry.getValue().equals(SimplePolynomial.ONE)) {
                                            return null;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                TRSTerm label;
                if (rewritePlus) {
                    label = this.transformVP(labMMP);
                    if (label == null) {
                        return null;
                    }
                }
                else {
                    label = this.transformMMP(labMMP);
                }
                result = new Pair<TRSTerm, TRSTerm>(label, labfApp);
            }
        }
        return result;
    }

    private Pair<TRSTerm, TRSTerm> processTermOfRhs(TRSTerm t) {
        Pair<TRSTerm, TRSTerm> result;
        if (t.isVariable()) {
            TRSVariable v = (TRSVariable)t;
            String newName = this.variableRenaming.get(v.getName());
            if (newName == null) {
                newName = this.variableFreshGen.getFreshName(v.getName(), false);
                this.variableRenaming.put(v.getName(), newName);
            }
            result = new Pair<TRSTerm, TRSTerm>(TRSTerm.createVariable(newName), t);
        }
        else {
            Map<String, VarPolynomial> varRenaming = new HashMap<String, VarPolynomial>();
            TRSFunctionApplication fApp = (TRSFunctionApplication)t;
            Set<TRSVariable> vars = fApp.getVariables();
            for (TRSVariable v : vars) {
                String newName = this.variableRenaming.get(v.getName());
                if (newName == null) {
                    newName = this.variableFreshGen.getFreshName(v.getName(), false);
                    this.variableRenaming.put(v.getName(), newName);
                }
                varRenaming.put(v.getName(), VarPolynomial.createVariable(newName));
            }
            FunctionSymbol fSym = fApp.getRootSymbol();
            int arity = fSym.getArity();
            if (arity == 0) {
                MaxMinPolynomial labMMP = this.actualModel.calculateMMpolyOfTermWithVarRenaming(t, varRenaming);
                TRSTerm label = this.transformMMP(labMMP);
                result = new Pair<TRSTerm, TRSTerm>(label, fApp);
            } else {
                ImmutableList<? extends TRSTerm> args = fApp.getArguments();
                int position = 0;
                ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>((2 * arity));
                for (int i = 0; i < (2 * arity); i++) {
                    newArgs.add(null);
                }
                for (TRSTerm arg : args) {
                    Pair<TRSTerm, TRSTerm> pair = this.processTermOfRhs(arg);
                    newArgs.set(position, pair.x);
                    newArgs.set((position + arity), pair.y);
                    position++;
                }
                TRSFunctionApplication labfApp =
                    TRSTerm.createFunctionApplication(
                        FunctionSymbol.create(fSym.getName(), (2 * arity)),
                        ImmutableCreator.create(newArgs));
                MaxMinPolynomial labMMP;
                if (arity > 2) {
                    TRSTerm tTrans = this.termMap.get(t);
                    labMMP = this.actualModel.calculateMMpolyOfTermWithVarRenaming(tTrans, varRenaming);
                } else {
                    labMMP = this.actualModel.calculateMMpolyOfTermWithVarRenaming(t, varRenaming);
                }
                TRSTerm label = this.transformMMP(labMMP);
                result = new Pair<TRSTerm, TRSTerm>(label, labfApp);
            }
        }
        return result;
    }

    public Set<Rule> calculateDecreasingRules() {
        LinkedHashSet<Rule> decrRules = new LinkedHashSet<Rule>();

        for (FunctionSymbol f : this.signature) {
            this.variableFreshGen.setUsedToOrigin();
            int arity = f.getArity();
            if (arity > 0) {
                FunctionSymbol newF = FunctionSymbol.create(f.getName(), (2 * arity));
                ArrayList<TRSTerm> args = new ArrayList<TRSTerm>(2 * arity);
                for (int i = 0; i < arity; i++) {
                    /*
                    String s = "x"+i;
                    Term labArg = Term.createVariable(s);
                    args.add(i, labArg);
                    */
                    TRSTerm arg = TRSTerm.createVariable(this.variableFreshGen.getFreshName(f.getName(), false));
                    args.add(i, arg);
                }
                for (int j = arity; j < (2 * arity); j++) {
                    String s = "y" + (j - arity);
                    TRSTerm arg = TRSTerm.createVariable(s);
                    args.add(j, arg);
                }
                TRSFunctionApplication rhs =
                    TRSTerm.createFunctionApplication(
                        newF,
                        ImmutableCreator.create(args));
                for (int k = 0; k < arity; k++) {
                    ArrayList<TRSTerm> increasedArgs = new ArrayList<TRSTerm>(args);
                    TRSVariable v = (TRSVariable)increasedArgs.remove(k);
                    ArrayList<TRSTerm> succdummy = new ArrayList<TRSTerm>(1);
                    succdummy.add(TRSTerm.createVariable(v.getName()));
                    TRSTerm successor = TRSTerm.createFunctionApplication(
                        this.SUC,
                        ImmutableCreator.create(succdummy));
                    increasedArgs.add(k, successor);
                    TRSFunctionApplication lhs =
                        TRSTerm.createFunctionApplication(
                            newF,
                            ImmutableCreator.create(increasedArgs));
                    decrRules.add(Rule.create(lhs, rhs));
                }
            }
        }
        return decrRules;
    }

    public Set<Rule> calculateLabelRules() {
        Set<Rule> labelRules = new HashSet<Rule>();
        TRSTerm sucX = MyLabeller.createSuc(this.varX, this.SUC);
        TRSTerm sucY = MyLabeller.createSuc(this.varY, this.SUC);

        //Arguments
        //[x, 0]
        ArrayList<TRSTerm> a1 = new ArrayList<TRSTerm>(2);
        a1.add(this.varX);
        a1.add(this.ZERO);
        ImmutableArrayList<TRSTerm> immuArray1 =
            ImmutableCreator.create(a1);

        //[0, y]
        ArrayList<TRSTerm> a2 = new ArrayList<TRSTerm>(2);
        a2.add(this.ZERO);
        a2.add(this.varY);
        ImmutableArrayList<TRSTerm> immuArray2 =
            ImmutableCreator.create(a2);

        //[x, y]
        ArrayList<TRSTerm> a3 = new ArrayList<TRSTerm>(2);
        a3.add(this.varX);
        a3.add(this.varY);
        ImmutableArrayList<TRSTerm> immuArray3 =
            ImmutableCreator.create(a3);

        //[x, s(y)]
        ArrayList<TRSTerm> a4 = new ArrayList<TRSTerm>(2);
        a4.add(this.varX);
        a4.add(sucY);
        ImmutableArrayList<TRSTerm> immuArray4 =
            ImmutableCreator.create(a4);

        //[s(x), y]
        ArrayList<TRSTerm> a5 = new ArrayList<TRSTerm>(2);
        a5.add(sucX);
        a5.add(this.varY);
        ImmutableArrayList<TRSTerm> immuArray5 =
            ImmutableCreator.create(a5);

        //[s(x), s(y)]
        ArrayList<TRSTerm> a6 = new ArrayList<TRSTerm>(2);
        a6.add(sucX);
        a6.add(sucY);
        ImmutableArrayList<TRSTerm> immuArray6 =
            ImmutableCreator.create(a6);

        //Plus Rules :
        //plus(x, 0) -> x
        labelRules.add(Rule.create(
            TRSTerm.createFunctionApplication(this.PLUS, immuArray1),
            this.varX));

        //plus(0, y) -> y
        labelRules.add(Rule.create(
            TRSTerm.createFunctionApplication(this.PLUS, immuArray2),
            this.varY));

        //plus(x, s(y)) -> s(plus(x, y))
        TRSFunctionApplication lhs = TRSTerm.createFunctionApplication(
            this.PLUS, immuArray4);
        ArrayList<TRSTerm> plusXY = new ArrayList<TRSTerm>(1);
        plusXY.add(TRSTerm.createFunctionApplication(this.PLUS, immuArray3));
        TRSFunctionApplication rhs = TRSTerm.createFunctionApplication(
            this.SUC, ImmutableCreator.create(plusXY));

        labelRules.add(Rule.create(lhs, rhs));

        //plus(s(x), y) -> s(plus(x, y))
        lhs = TRSTerm.createFunctionApplication(this.PLUS, immuArray5);
        rhs = TRSTerm.createFunctionApplication(this.SUC, ImmutableCreator.create(plusXY));
        labelRules.add(Rule.create(lhs, rhs));

        //Times Rules :
        //times(x, 0) -> 0
        labelRules.add(Rule.create(
            TRSTerm.createFunctionApplication(this.TIMES, immuArray1),
            this.ZERO));

        //times(0, y) -> 0
        labelRules.add(Rule.create(
            TRSTerm.createFunctionApplication(this.TIMES, immuArray2),
            this.ZERO));

        //times(x, s(y)) -> plus(x, times(x, y))
        lhs = TRSTerm.createFunctionApplication(this.TIMES, immuArray4);
        ArrayList<TRSTerm> x_timesXY = new ArrayList<TRSTerm>(2);
        x_timesXY.add(this.varX);
        x_timesXY.add(TRSTerm.createFunctionApplication(this.TIMES, immuArray3));
        rhs = TRSTerm.createFunctionApplication(
            this.PLUS, ImmutableCreator.create(x_timesXY));
        labelRules.add(Rule.create(lhs, rhs));

        //times(s(x), y) -> plus(y, times(x, y))
        lhs = TRSTerm.createFunctionApplication(this.TIMES, immuArray5);
        ArrayList<TRSTerm> y_timesXY = new ArrayList<TRSTerm>(2);
        y_timesXY.add(this.varY);
        y_timesXY.add(TRSTerm.createFunctionApplication(this.TIMES, immuArray3));
        rhs = TRSTerm.createFunctionApplication(
            this.PLUS, ImmutableCreator.create(y_timesXY));
        labelRules.add(Rule.create(lhs, rhs));

        //Max Rules
        //max(x, 0) -> x
        labelRules.add(Rule.create(TRSTerm.createFunctionApplication(this.MAX, immuArray1), this.varX));

        //max(0, y) -> y
        labelRules.add(Rule.create(TRSTerm.createFunctionApplication(this.MAX, immuArray2), this.varY));

        //max(s(x), s(y)) -> s(max(x, y))
        ArrayList<TRSTerm> maxXY = new ArrayList<TRSTerm>(1);
        maxXY.add(TRSTerm.createFunctionApplication(this.MAX, immuArray3));
        rhs = TRSTerm.createFunctionApplication(this.SUC,
            ImmutableCreator.create(maxXY));
        labelRules.add(Rule.create(
            TRSTerm.createFunctionApplication(this.MAX, immuArray6), rhs));

        //Min Rules
        //min(x, 0) -> 0
        labelRules.add(Rule.create(TRSTerm.createFunctionApplication(this.MIN, immuArray1), this.ZERO));

        //min(0, y) -> 0
        labelRules.add(Rule.create(TRSTerm.createFunctionApplication(this.MIN, immuArray2), this.ZERO));

        //min(s(x), s(y)) -> s(min(x, y))
        ArrayList<TRSTerm> minXY = new ArrayList<TRSTerm>(1);
        minXY.add(TRSTerm.createFunctionApplication(this.MIN, immuArray3));
        rhs = TRSTerm.createFunctionApplication(this.SUC,
            ImmutableCreator.create(minXY));
        labelRules.add(Rule.create(
            TRSTerm.createFunctionApplication(this.MIN, immuArray6), rhs));

        return labelRules;
    }

    private TRSTerm transformMMP(MaxMinPolynomial mmp) {
        if (Globals.DEBUG_PATWIE) {
            if (mmp == null) {
                System.out.println();
            }
        }
        MMPolyMetaInf metaInf = mmp.getMetaInf();
        switch (metaInf) {
            case Constant: {
                int value = mmp.getVarPolynomial().getConstantPart().getNumericalAddend().intValue();
                return this.calculateNumber(value);

            }
            case VarPoly: {
                ArrayList<TRSTerm> addends = new ArrayList<TRSTerm>();
                VarPolynomial vp = mmp.getVarPolynomial();
                Set<Entry<IndefinitePart, SimplePolynomial>> entries = vp.getVarMonomials().entrySet();
                for (Entry<IndefinitePart, SimplePolynomial> entry : entries) {
                    addends.add(this.calculateAddend(entry));
                }
                return this.calculateBalancedTerm(this.PLUS, addends);
            }
            case MinInterpretation: {
                ArrayList<TRSTerm> vpList = new ArrayList<TRSTerm>();
                ImmutableSet<VarPolynomial> vps = mmp.getAllMinTerms();
                for (VarPolynomial vp : vps) {
                    ArrayList<TRSTerm> addends = new ArrayList<TRSTerm>();
                    Set<Entry<IndefinitePart, SimplePolynomial>> entries = vp.getVarMonomials().entrySet();
                    for (Entry<IndefinitePart, SimplePolynomial> entry : entries) {
                        addends.add(this.calculateAddend(entry));
                    }
                    vpList.add(this.calculateBalancedTerm(this.PLUS, addends));
                }
                return this.calculateBalancedTerm(this.MIN, vpList);
            }
            case MaxInterpretation: {
                ArrayList<TRSTerm> minList = new ArrayList<TRSTerm>();
                ImmutableSet<? extends ImmutableSet<VarPolynomial>> minSets = mmp.getAllMinSets();
                for (ImmutableSet<VarPolynomial> vps : minSets) {
                    ArrayList<TRSTerm> vpList = new ArrayList<TRSTerm>();
                    for (VarPolynomial vp : vps) {
                        ArrayList<TRSTerm> addends = new ArrayList<TRSTerm>();
                        Set<Entry<IndefinitePart, SimplePolynomial>> entries = vp.getVarMonomials().entrySet();
                        for (Entry<IndefinitePart, SimplePolynomial> entry : entries) {
                            addends.add(this.calculateAddend(entry));
                        }
                        vpList.add(this.calculateBalancedTerm(this.PLUS, addends));
                    }
                    minList.add(this.calculateBalancedTerm(this.MIN, vpList));
                }
                return this.calculateBalancedTerm(this.MAX, minList);
            }
            default: {
                if (Globals.useAssertions) {
                    throw new RuntimeException("The enum MMPolyMetaInf has been modified!");
                }
            }
        }

        return null;
    }

    private TRSTerm calculateSuccTerm(TRSVariable var, int value) {
        ArrayList<TRSTerm> argsArray = new ArrayList<TRSTerm>(1);
        TRSTerm auxTerm = var;
        if (value != 0) {
            argsArray.add(auxTerm);;
            while (value > 0) {
                ArrayList<TRSTerm> argument = new ArrayList<TRSTerm>(1);
                argument.add(argsArray.get(0));
                ImmutableArrayList<TRSTerm> immuArray = ImmutableCreator.create(argument); //argsArray
                auxTerm = TRSTerm.createFunctionApplication(
                    this.SUC, immuArray);
                argsArray.clear();
                argsArray.add(0, auxTerm);
                value--;
            }
        }
        return auxTerm;
    }

    private TRSTerm calculateNumber(int value) {
        ArrayList<TRSTerm> argsArray = new ArrayList<TRSTerm>(10);
        TRSTerm auxTerm = this.ZERO;
        if (value != 0) {
            argsArray.add(auxTerm);;
            while (value > 0) {
                ArrayList<TRSTerm> argument = new ArrayList<TRSTerm>(1);
                argument.add(argsArray.get(0));
                ImmutableArrayList<TRSTerm> immuArray = ImmutableCreator.create(argument); //argsArray
                auxTerm = TRSTerm.createFunctionApplication(
                    this.SUC, immuArray);
                argsArray.clear();
                argsArray.add(0, auxTerm);
                value--;
            }
        }
        return auxTerm;
    }

    private TRSTerm calculateAddend(Entry<IndefinitePart, SimplePolynomial> entry) {
        TRSTerm auxTerm;
        TRSTerm product;
        ArrayList<TRSTerm> multiplicants = new ArrayList<TRSTerm>();
        IndefinitePart inDef = entry.getKey();
        SimplePolynomial sp = entry.getValue();
        Set<String> inDefNames = inDef.getIndefinites();
        for (String inDefName : inDefNames) {
            int exp = inDef.getExponent(inDefName);
            if (Globals.useAssertions) {
                assert (exp != 0);
            }
            if (exp > 1) {
                multiplicants.add(this.calculateBalancedTerm(this.TIMES, TRSTerm.createVariable(inDefName), exp));
            }
            else { // exp==1
                auxTerm = TRSTerm.createVariable(inDefName);
                multiplicants.add(auxTerm);
            }
        }
        if (Globals.useAssertions) {
            assert (sp.isConstant());
        }
        TRSTerm factor = this.calculateNumber(sp.getNumericalAddend().intValue());
        if (multiplicants.size() == 0 || (!factor.equals(this.ONE))) {
            multiplicants.add(0, factor);
        }
        product = this.calculateBalancedTerm(this.TIMES, multiplicants);
        return product;
    }

    private TRSTerm calculateBalancedTerm(FunctionSymbol fSym, List<TRSTerm> args) {
        ArrayList<TRSTerm> values = new ArrayList<TRSTerm>(2);
        if (Globals.useAssertions) {
            assert (fSym.getArity() == 2);
            assert (args.size() > 0);
        }
        int numberOfArgs = args.size();
        if (numberOfArgs == 2) {
            values.addAll(args);
            return TRSTerm.createFunctionApplication(fSym,
                ImmutableCreator.create(values));
        }
        if (numberOfArgs > 2) {
            int half;
            if ((numberOfArgs % 2) == 0) {
                half = (numberOfArgs / 2);
            }
            else {
                half = ((numberOfArgs / 2) + 1);
            }
            values.add(0, this.calculateBalancedTerm(fSym, args.subList(0, half)));
            values.add(1, this.calculateBalancedTerm(fSym, args.subList(half, numberOfArgs)));
            return TRSTerm.createFunctionApplication(fSym,
                ImmutableCreator.create(values));
        }
        else {
            if (Globals.useAssertions) {
                assert (args.size() == 1);
            }
            return args.get(0);
        }
    }

    private TRSTerm calculateBalancedTerm(FunctionSymbol fSym, TRSTerm t, int power) {
        if (Globals.useAssertions) {
            assert (fSym.getArity() == 2);
            assert (power > 0);
        }
        ArrayList<TRSTerm> values = new ArrayList<TRSTerm>(2);
        if (power == 2) {
            values.add(t);
            values.add(t);
            return TRSTerm.createFunctionApplication(fSym,
                ImmutableCreator.create(values));
        }
        if (power > 2) {
            int half = (power / 2);
            if ((power % 2) == 0) {
                TRSTerm result = this.calculateBalancedTerm(fSym, t, half);
                values.add(0, result);
                values.add(1, result);
                return TRSTerm.createFunctionApplication(fSym,
                    ImmutableCreator.create(values));
            }
            else {
                values.add(0, this.calculateBalancedTerm(fSym, t, (half + 1)));
                values.add(1, this.calculateBalancedTerm(fSym, t, half));
                return TRSTerm.createFunctionApplication(fSym,
                    ImmutableCreator.create(values));

            }
        }
        else {
            if (Globals.useAssertions) {
                assert (power == 1);
            }
            return t;
        }
    }

    private TRSTerm transformVP(MaxMinPolynomial mmp) {
        boolean rewritingPossible = true;
        TRSTerm result;
        if (Globals.useAssertions) {
            assert (mmp.getMetaInf() == MMPolyMetaInf.VarPoly) : "MyLabeller : compensatePlus: MaxMinPolynomial is not an encapsulated VarPolynomial.";
        }
        VarPolynomial vp = mmp.getVarPolynomial();
        Set<Entry<IndefinitePart, SimplePolynomial>> entries = vp.getVarMonomials().entrySet();
        if (Globals.useAssertions) {
            assert (entries.size() == 2) : "MyLabeller : compensatePlus: VarPolynomial does not have 2 monomials.";
            Iterator<Entry<IndefinitePart, SimplePolynomial>> iter = entries.iterator();
            while (iter.hasNext()) {
                Entry<IndefinitePart, SimplePolynomial> entry = iter.next();
                // assert(entry.getKey().isIndefinite()) : "MyLabeller : compensatePlus: An IndefinitePart of the Varpolynomial is not just an indefinite.";
                assert (entry.getValue().isConstant()) : "MyLabeller : compensatePlus: A SimplePolynomial of the Varpolynomial is not a Constant.";
            }
        }
        Iterator<Entry<IndefinitePart, SimplePolynomial>> iter = entries.iterator();
        TRSVariable var = null;
        int i = 0;
        while (iter.hasNext()) {
            Entry<IndefinitePart, SimplePolynomial> entry = iter.next();
            if (entry.getKey().isEmpty()) {
                if (i != 0) {
                    rewritingPossible = false;
                }
                i = entry.getValue().getNumericalAddend().intValue();
            }
            else {
                if (var != null) {
                    rewritingPossible = false;
                }
                var = TRSTerm.createVariable(entry.getKey().getIndefinites().iterator().next());
            }
        }
        if (!rewritingPossible) {
            return null;
        }
        result = this.calculateSuccTerm(var, i);
        return result;
    }

}
