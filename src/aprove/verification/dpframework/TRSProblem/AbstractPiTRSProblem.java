package aprove.verification.dpframework.TRSProblem;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

abstract public class AbstractPiTRSProblem extends
    DefaultBasicObligation implements Exportable,
        PLAIN_Able, HTML_Able, HasTRSTerms {

    private final ImmutableSet<GeneralizedRule> R;
    private final ImmutableAfs Pi;

    /* cached / calculated values */
    private final int hashCode;
    //    private MemoryIterable<ImmutableTriple<Term, Term, Boolean>> critPairs;
    private volatile ImmutableSet<FunctionSymbol> signature; // signature of R
    //    private ImmutableSet<FunctionSymbol> Rsignature;       // signature of R
    private volatile ImmutableSet<FunctionSymbol> defSymbolsOfR; // the same as ruleMap.keySet();
    private volatile ImmutableMap<FunctionSymbol, ImmutableSet<GeneralizedRule>> ruleMap;
    //    private ImmutableMap<FunctionSymbol, ImmutableSet<Rule>> reverseRuleMap;
    //    private ImmutableSet<Rule> lhsWhereRhsIsVariable;
    private volatile ImmutableSet<GeneralizedRule> dps; // the dps of this TRS
    volatile Map<FunctionSymbol, FunctionSymbol> defToTup;

    //    private ApplicativeInfo applicativeInfo;
    //    private YNM isRRRQreducable;

    protected AbstractPiTRSProblem(String shortName, String longName,
            ImmutableSet<GeneralizedRule> R, ImmutableAfs Pi) {
        super(shortName, longName);
        if (Globals.useAssertions) {
            assert (AbstractPiTRSProblem.checkConstructorArgs(R, Pi));
        }
        this.R = R;
        this.Pi = Pi;
        this.hashCode = R.hashCode() * 849033 + Pi.hashCode() * 84903 + 8490213;
        //      this.critPairs = null;
        //      this.signature = null;
        //      this.Rsignature = null;
        //      this.defSymbolsOfR = null;
        //      this.ruleMap = null;
        //      this.reverseRuleMap = null;
        //      this.lhsWhereRhsIsVariable = null;
        //      this.applicativeInfo = null;
        //      this.isRRRQreducable = isRRRQreducable;
    }

    private static boolean checkConstructorArgs(ImmutableSet<GeneralizedRule> R,
        ImmutableAfs Pi) {
        return R != null && Pi != null;
    }

    /*- accessors ------------------------------------------------------------*/

    public ImmutableSet<GeneralizedRule> getR() {
        return this.R;
    }

    /**
     * get R as a mapping from defined symbols to corresponding rules
     */
    public ImmutableMap<FunctionSymbol, ImmutableSet<GeneralizedRule>> getRuleMap() {
        if (this.ruleMap == null) {
            synchronized (this) {
                if (this.ruleMap == null) {
                    this.calculateDefSymbolsAndRuleMap();
                }
            }
        }
        return this.ruleMap;
    }

    public ImmutableSet<FunctionSymbol> getDefinedSymbolsOfR() {
        if (this.defSymbolsOfR == null) {
            synchronized (this) {
                if (this.defSymbolsOfR == null) {
                    this.calculateDefSymbolsAndRuleMap();
                }
            }
        }
        return this.defSymbolsOfR;
    }

    public ImmutableSet<FunctionSymbol> getSignature() {
        if (this.signature == null) {
            this.computeSignature();
        }
        return this.signature;
    }

    public ImmutableAfs getPi() {
        return this.Pi;
    }

    /**
     * returns the set of DPs of this TRS
     */
    public Pair<ImmutableSet<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>> getDPs() {
        if (this.dps == null) {
            synchronized (this) {
                if (this.dps == null) {
                    Set<GeneralizedRule> dps =
                        new LinkedHashSet<GeneralizedRule>();
                    Set<FunctionSymbol> signature =
                        new LinkedHashSet<FunctionSymbol>(this.getSignature());
                    Set<FunctionSymbol> defs = this.getDefinedSymbolsOfR();
                    this.defToTup =
                        new LinkedHashMap<FunctionSymbol, FunctionSymbol>();

                    for (GeneralizedRule rule : this.R) {
                        Set<TRSFunctionApplication> dpRhss =
                            new LinkedHashSet<TRSFunctionApplication>();
                        TRSFunctionApplication lhs = rule.getLeft();
                        TRSTerm rhs = rule.getRight();
                        // get all subterms of rhs of actRule which have a defined symbol as root
                        for (TRSFunctionApplication subterm : rhs.getNonVariableSubTerms()) {
                            FunctionSymbol actFuncSym = subterm.getRootSymbol();
                            if (defs.contains(actFuncSym)) {
                                if (!lhs.hasProperSubterm(subterm)) {
                                    dpRhss.add(subterm);
                                }
                            }
                        }

                        if (dpRhss.isEmpty()) {
                            continue;
                        }

                        FunctionSymbol tf =
                            AbstractPiTRSProblem.getTupleSymbol(
                                lhs.getRootSymbol(), this.defToTup, signature);
                        TRSFunctionApplication tlhs =
                            TRSTerm.createFunctionApplication(tf,
                                lhs.getArguments());

                        for (TRSFunctionApplication dpRhs : dpRhss) {
                            FunctionSymbol tg =
                                AbstractPiTRSProblem.getTupleSymbol(
                                    dpRhs.getRootSymbol(), this.defToTup,
                                    signature);
                            TRSFunctionApplication trhs =
                                TRSTerm.createFunctionApplication(tg,
                                    dpRhs.getArguments());
                            dps.add(GeneralizedRule.create(tlhs, trhs));
                        }

                    }

                    this.dps = ImmutableCreator.create(dps);

                }
            }
        }
        return new Pair<ImmutableSet<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>>(
            this.dps, this.defToTup);
    }

    /**
     * returns the set of terms in R, the set may be modified
     */
    @Override
    public Set<TRSTerm> getTerms() {
        // terms of R
        Set<TRSTerm> terms = CollectionUtils.getTerms(this.R);
        return terms;
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        throw new UnsupportedOperationException();
    }

    /*- abstract methods -----------------------------------------------------*/

    abstract public String getName();

    @Override
    abstract public String export(Export_Util o);

    /*- export ---------------------------------------------------------------*/

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public String toHTML() {
        return this.export(new HTML_Util());
    }

    @Override
    public String toPLAIN() {
        return this.export(new PLAIN_Util());
    }

    /*- Object methods -------------------------------------------------------*/

    @Override
    public boolean equals(Object oth) {
        if (this == oth) {
            return true;
        }

        if (oth == null) {
            return false;
        }

        if (oth.getClass() != this.getClass()) {
            return false;
        }

        AbstractPiTRSProblem other = (AbstractPiTRSProblem) oth;
        if (!this.R.equals(other.R)) {
            return false;
        }

        return this.Pi.equals(other.Pi);
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

    /*- private methods ------------------------------------------------------*/

    private void calculateDefSymbolsAndRuleMap() {
        Map<FunctionSymbol, Set<GeneralizedRule>> ruleMap =
            new LinkedHashMap<FunctionSymbol, Set<GeneralizedRule>>();
        for (GeneralizedRule rule : this.R) {
            FunctionSymbol f = rule.getRootSymbol();
            Set<GeneralizedRule> fRules = ruleMap.get(f);
            if (fRules == null) {
                fRules = new LinkedHashSet<GeneralizedRule>();
                ruleMap.put(f, fRules);
            }
            fRules.add(rule);
        }
        // make immutable
        Map<FunctionSymbol, ImmutableSet<GeneralizedRule>> immutableMap =
            new HashMap<FunctionSymbol, ImmutableSet<GeneralizedRule>>();
        for (Map.Entry<FunctionSymbol, Set<GeneralizedRule>> entry : ruleMap.entrySet()) {
            immutableMap.put(entry.getKey(),
                ImmutableCreator.create(entry.getValue()));
        }
        this.ruleMap = ImmutableCreator.create(immutableMap);
        this.defSymbolsOfR = ImmutableCreator.create(immutableMap.keySet());
    }

    private synchronized void computeSignature() {
        if (this.signature == null) {
            Set<FunctionSymbol> signature =
                CollectionUtils.getFunctionSymbols(this.R);
            this.signature = ImmutableCreator.create(signature);
        }
    }

    /**
     * looksup a tuple symbol for a defined symbol f. If it is not defined, a
     * new symbol is created (which is not contained in allSyms) and the mapping
     * is stored, and the new symbol is added to allSyms
     * @param f
     * @param defToTup
     * @param allSyms
     * @return
     */
    private static FunctionSymbol getTupleSymbol(FunctionSymbol f,
        Map<FunctionSymbol, FunctionSymbol> defToTup,
        Set<FunctionSymbol> allSyms) {
        FunctionSymbol tf = defToTup.get(f);
        if (tf == null) {
            String wishedName = f.getName().toUpperCase();
            int arity = f.getArity();
            int nr = 1;
            tf = FunctionSymbol.create(wishedName, arity);
            while (!allSyms.add(tf)) {
                tf = FunctionSymbol.create(wishedName + "^" + nr, arity);
                nr++;
            }

            defToTup.put(f, tf);
        }
        return tf;
    }

    /*- old methods ----------------------------------------------------------*/

    /*public Iterable<ImmutableTriple<Term, Term, Boolean>> getCriticalPairs() {
    if (this.critPairs == null) {
        synchronized(this) {
            if (this.critPairs == null) {
                if (!this.Q.isEmpty()) {
                    System.out.println("Perhaps use special Q-critical pairs for non-empty Q");
                }
                this.critPairs = new MemoryIterable<ImmutableTriple<Term, Term, Boolean>>(Rule.getCriticalPairs(this.R));
            }
        }
    }
    return this.critPairs;
    }*/

    /*private void calculateReverseRuleMap() {
        Map<FunctionSymbol, Set<Rule>> reverseRuleMap = new HashMap<FunctionSymbol, Set<Rule>>();
        for (Rule rule : this.R) {
            Term rhs = rule.getRight();
            if(rhs.isVariable()) {
                continue;
            }
            else {
                FunctionApplication fa = (FunctionApplication) rhs;
                FunctionSymbol fs = fa.getRootSymbol();

                Set<Rule> fsRules = reverseRuleMap.get(fs);
                if (fsRules == null) {
                    fsRules = new LinkedHashSet<Rule>();
                    reverseRuleMap.put(fs, fsRules);
                }
                fsRules.add(rule);
            }
        }
        Map<FunctionSymbol, ImmutableSet<Rule>> immutableMap = new HashMap<FunctionSymbol, ImmutableSet<Rule>>();
        for (Map.Entry<FunctionSymbol, Set<Rule>> entry : reverseRuleMap.entrySet()) {
            immutableMap.put(entry.getKey(), ImmutableCreator.create(entry.getValue()));
        }
        this.reverseRuleMap = ImmutableCreator.create(immutableMap);
    }*/

    /**
     * get R^{-1} as a mapping from function symbols of rhs to corresponding
     * rules
     */
    /*public ImmutableMap<FunctionSymbol, ImmutableSet<Rule>> getReverseRuleMap() {
        if(this.reverseRuleMap == null) {
            synchronized(this) {
                if(this.reverseRuleMap == null) {
                    this.calculateReverseRuleMap();
                }
            }
        }
        return this.reverseRuleMap;
    }*/

    /**
     * get all rules where the rhs is a variable
     */
    /*public ImmutableSet<Rule> getRulesWhereRhsIsVariable() {
        Set<Rule> rhsVar = new LinkedHashSet<Rule>();
        if(this.lhsWhereRhsIsVariable == null) {
            for(Rule rule : this.R) {
                if(rule.getRight().isVariable()) {
                    rhsVar.add(rule);
                }
            }
            this.lhsWhereRhsIsVariable = ImmutableCreator.create(rhsVar);
        }
        return this.lhsWhereRhsIsVariable;
    }*/

    /**
     * get the Applicative Info that has information like
     * @return
     */
    /*public ApplicativeInfo getApplicativeInfo() {
        if (this.applicativeInfo == null) {
            synchronized(this) {
                if (this.applicativeInfo == null) {
                    this.applicativeInfo = ApplicativeInfo.create(this.getTerms());
                }
            }
        }
        return this.applicativeInfo;
    }*/

    /**
     * checks whether this can be A-transformed
     */
    /*public boolean isATransformable() {
        return this.getApplicativeInfo().aTransformable;
     }*/

    /**
     * returns the A-Transformed Q-TRS. Note that Q is deleted, if Q is not a
     * superset of lhs(R). Throws a runtime exception if this is not
     * A-tranformable.
     */
    /*public PiTRSProblem getATransformed() {
        ApplicativeInfo aInfo = this.getApplicativeInfo();
        if (!aInfo.aTransformable) {
            throw new RuntimeException("This is not A-Transformable");
        }

        Set<Rule> aR = aInfo.transformRules(this.R);
        QTermSet newQ;
        YNM isRRRQreducable = this.isRRRQreducable;
        if (this.Q.isEmpty()) {
            newQ = this.Q;
        } else {
            Set<FunctionApplication> aQ;
            if (this.QsupersetOfLhsR()) {
                aQ = aInfo.transformFunctionApplications(this.Q.getTerms());
            } else {
                aQ = new LinkedHashSet<FunctionApplication>();
                isRRRQreducable = YNM.NO;
            }
            newQ = new QTermSet(aQ);
        }
        return new PiTRSProblem(ImmutableCreator.create(aR), newQ, this.QsuperR, isRRRQreducable);
    }*/

    /**
     * checks whether a lhs of R contains a Q redex below the root
     * @return
     */
    /*public boolean isRRRQreducable() {
        if (this.isRRRQreducable == YNM.MAYBE) {
            synchronized(this) {
                if (this.isRRRQreducable == YNM.MAYBE) {
                    if (!this.Q.isEmpty()) {
                        for (Rule rule : this.R) {
                            for (Term subTerm : rule.getLeft().getArguments()) {
                                if (Q.canBeRewritten(subTerm)) {
                                    this.isRRRQreducable = YNM.YES;
                                    return true;
                                }
                            }
                        }
                    }
                    this.isRRRQreducable = YNM.NO;
                }
            }
        }
        return this.isRRRQreducable.toBool();
    }*/

    /**
     * set the RRR-Q reducable flag by hand
     * @param value
     */
    /*public void setRRRQreducable(boolean value) {
        if (Globals.useAssertions) {
            assert(this.isRRRQreducable() == value);
        }
        this.isRRRQreducable = YNM.fromBool(value);
    }*/
}
