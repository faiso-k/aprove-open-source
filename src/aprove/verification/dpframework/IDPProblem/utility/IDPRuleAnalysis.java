/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.utility;

import java.util.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.Processors.algorithms.usableRules.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * Combines the {@see RuleAnalysis} of the r and q rules.
 * @author mpluecke
 *
 */
public class IDPRuleAnalysis implements Immutable, HasTRSTerms {

    /**
     * Creates an IDPRuleAnalysis with empty P (e.g., from ITRSs). WARNING: this can not be used to convert an ITRS to an IDP.
     */
    public static IDPRuleAnalysis createFromR(RuleAnalysis<GeneralizedRule> RAnalysis, IQTermSet Q) {
        return new IDPRuleAnalysis(RAnalysis, new RuleAnalysis<GeneralizedRule>(ImmutableCreator.create(Collections.<GeneralizedRule>emptySet()), RAnalysis.getPreDefinedMap()), Q, null);
    }

    private final RuleAnalysis<GeneralizedRule> pAnalysis;
    private final RuleAnalysis<GeneralizedRule> rAnalysis;
    private final IQTermSet Q;
    private final Map <IUsableRulesEstimation.Estimations, IdpQUsableRules> useableRules;

    private volatile ImmutableSet<Domain> domains;
    private volatile ImmutableSet<FunctionSymbol> functionSymbols;
    private volatile ImmutableSet<TRSVariable> variables;
    private volatile ImmutableSet<FunctionSymbol> definedSymbols;
    private volatile ImmutableSet<TRSFunctionApplication> leftHandSides;
    private volatile ImmutableSet<TRSTerm> terms;
    private volatile Boolean NfQSubsetEqNfR;
    private volatile ImmutableSet<FunctionSymbol> headSymbols;
    private volatile ImmutableSet<FunctionSymbol> functionSymbolsPRNoHead;
    private volatile ImmutableMap<FunctionSymbol, ImmutableSet<GeneralizedRule>> ruleMap;
    private volatile ImmutableSet<GeneralizedRule> rules;
    private final IDPPredefinedMap predefinedMap;
    private final Map<FunctionSymbol, ImmutableSet<TRSFunctionApplication>> rootToLeftHandSides = new LinkedHashMap<FunctionSymbol, ImmutableSet<TRSFunctionApplication>>();

    public IDPRuleAnalysis(ImmutableSet<GeneralizedRule> r, ImmutableSet<GeneralizedRule> p, IQTermSet Q, Map <IUsableRulesEstimation.Estimations, IdpQUsableRules>  useableRules) {
        this.predefinedMap = Q.getPreDefinedMap();
        this.rAnalysis = new RuleAnalysis<GeneralizedRule>(r, this.predefinedMap);
        this.pAnalysis = new RuleAnalysis<GeneralizedRule>(p, this.predefinedMap);
        this.Q = Q;
        this.useableRules = useableRules != null ? useableRules : new LinkedHashMap <IUsableRulesEstimation.Estimations, IdpQUsableRules> ();
    }

    public IDPRuleAnalysis(RuleAnalysis<GeneralizedRule> r, ImmutableSet<GeneralizedRule> p, IQTermSet Q, Map <IUsableRulesEstimation.Estimations, IdpQUsableRules>  useableRules) {
        this.rAnalysis = r;
        if (Globals.useAssertions) {
            assert(r.getPreDefinedMap().equals(Q.getPreDefinedMap())) : "pre defined maps must be identical";
        }
        this.predefinedMap = r.getPreDefinedMap();
        this.pAnalysis = new RuleAnalysis<GeneralizedRule>(p, this.predefinedMap);
        this.Q = Q;
        this.useableRules = useableRules != null ? useableRules : new LinkedHashMap <IUsableRulesEstimation.Estimations, IdpQUsableRules> ();
    }

    public IDPRuleAnalysis(ImmutableSet<GeneralizedRule> r, RuleAnalysis<GeneralizedRule> p, IQTermSet Q, Map <IUsableRulesEstimation.Estimations, IdpQUsableRules>  useableRules) {
        this.pAnalysis = p;
        if (Globals.useAssertions) {
            assert(p.getPreDefinedMap().equals(Q.getPreDefinedMap())) : "pre defined maps must be identical";
        }
        this.predefinedMap = p.getPreDefinedMap();
        this.rAnalysis = new RuleAnalysis<GeneralizedRule>(r, this.predefinedMap);
        this.Q = Q;
        this.useableRules = useableRules != null ? useableRules : new LinkedHashMap <IUsableRulesEstimation.Estimations, IdpQUsableRules> ();
    }

    public IDPRuleAnalysis(RuleAnalysis<GeneralizedRule> r, RuleAnalysis<GeneralizedRule> p, IQTermSet Q, Map <IUsableRulesEstimation.Estimations, IdpQUsableRules>  useableRules) {
        this.rAnalysis = r;
        this.pAnalysis = p;
        if (Globals.useAssertions) {
            assert(r.getPreDefinedMap().equals(p.getPreDefinedMap())) && r.getPreDefinedMap().equals(Q.getPreDefinedMap()) : "pre defined maps must be identical";
        }
        this.predefinedMap = r.getPreDefinedMap();
        this.Q = Q;
        this.useableRules = useableRules != null ? useableRules : new LinkedHashMap <IUsableRulesEstimation.Estimations, IdpQUsableRules> ();
    }

    /**
     * Extract all domain suffixes used in a Collection of rules.
     */
    public ImmutableSet<Domain> getDomains() {
        if (this.domains == null) {
            synchronized(this) {
                if (this.domains == null) {
                    Set<Domain> d = new LinkedHashSet<Domain>(this.rAnalysis.getDomains());
                    d.addAll(this.pAnalysis.getDomains());
                    return this.domains = ImmutableCreator.create(d);
                }
            }
        }
        return this.domains;
    }

    /**
     * Extracts all function symbols that occur in the rules.
     * @return the set of function symbols that occur in the rules.
     */
    public ImmutableSet<FunctionSymbol> getFunctionSymbols() {
        if (this.functionSymbols == null) {
            synchronized(this) {
                if (this.functionSymbols == null) {
                    Set<FunctionSymbol> f = new LinkedHashSet<FunctionSymbol>(this.rAnalysis.getFunctionSymbols());
                    f.addAll(this.pAnalysis.getFunctionSymbols());
                    return this.functionSymbols = ImmutableCreator.create(f);
                }
            }
        }
        return this.functionSymbols;
    }

    /**
     * @return true iff fs is a constructor
     */
    public Boolean isConstructor(FunctionSymbol fs) {
        ImmutableSet<FunctionSymbol> defined = this.getDefinedSymbols();
        if (defined.contains(fs)) {
            return false;
        }
        return this.predefinedMap.getPredefinedSemantics(fs) == null;
    }

    /**
     * Extracts all variables that occur in the rules.
     * @return the set of function symbols that occur in the rules.
     */
    public ImmutableSet<TRSVariable> getVariables() {
        if (this.variables == null) {
            synchronized(this) {
                if (this.variables == null) {
                    Set<TRSVariable> v = new LinkedHashSet<TRSVariable>(this.rAnalysis.getVariables());
                    v.addAll(this.pAnalysis.getVariables());
                    return this.variables = ImmutableCreator.create(v);
                }
            }
        }
        return this.variables;
    }

    /**
     * Determines the function symbols that are defined by the rules.
     * @return the set of function symbols that are defined.
     */
    public ImmutableSet<FunctionSymbol> getDefinedSymbols() {
        if (this.definedSymbols == null) {
            synchronized(this) {
                if (this.definedSymbols == null) {
                    Set<FunctionSymbol> d = new LinkedHashSet<FunctionSymbol>(this.rAnalysis.getDefinedSymbols());
                    d.addAll(this.pAnalysis.getDefinedSymbols());
                    return this.definedSymbols = ImmutableCreator.create(d);
                }
            }
        }
        return this.definedSymbols;
    }

    /**
     * Extracts the left hand sides of the rules.
     * @return left hand sides of the rules.
     */
    public ImmutableSet<TRSFunctionApplication> getLeftHandSides() {
        if (this.leftHandSides == null) {
            synchronized(this) {
                if (this.leftHandSides == null) {
                    Set<TRSFunctionApplication> l = new LinkedHashSet<TRSFunctionApplication>(this.rAnalysis.getLeftHandSides());
                    l.addAll(this.pAnalysis.getLeftHandSides());
                    return this.leftHandSides = ImmutableCreator.create(l);
                }
            }
        }
        return this.leftHandSides;
    }

    /**
     * Extracts the left hand sides of the rules that have a specific function symbol as root.
     * @param rootSymbol - the root symbol
     * @return left hand sides of the rules that have the specified root symbol.
     */
    public ImmutableSet<TRSFunctionApplication> getLeftHandSides(FunctionSymbol rootSymbol) {
        ImmutableSet<TRSFunctionApplication> lhss;
        synchronized(this.rootToLeftHandSides) {
            lhss = this.rootToLeftHandSides.get(rootSymbol);
            if (lhss == null) {
                Set<TRSFunctionApplication> tmp = new LinkedHashSet<TRSFunctionApplication>(this.rAnalysis.getLeftHandSides(rootSymbol));
                tmp.addAll(this.pAnalysis.getLeftHandSides(rootSymbol));
                lhss = ImmutableCreator.create(tmp);
                this.rootToLeftHandSides.put(rootSymbol, lhss);
            }
        }
        return lhss;
    }


    /**
     * Extracts all terms used in the ruled.
     * @return all terms used in the ruled.
     */
    @Override
    public Set<? extends TRSTerm> getTerms() {
        if (this.terms == null) {
            synchronized(this) {
                if (this.terms == null) {
                    Set<TRSTerm> t = new LinkedHashSet<TRSTerm>(this.rAnalysis.getTerms());
                    t.addAll(this.pAnalysis.getTerms());
                    return this.terms = ImmutableCreator.create(t);
                }
            }
        }
        return this.terms;
    }


    public IQTermSet getQ() {
        return this.Q;
    }

    public boolean isNfQSubsetEqNfR() {
        if (this.NfQSubsetEqNfR != null) {
            return this.NfQSubsetEqNfR;
        }
        this.NfQSubsetEqNfR = this.Q.canAllLhsBeRewritten(this.rAnalysis.getRules());
        return this.NfQSubsetEqNfR;
    }

    public ImmutableSet<FunctionSymbol> getHeadSymbols() {
        if (this.headSymbols == null) {
            this.computeHeadSignatures();
        }
        return this.headSymbols;
    }

    public ImmutableSet<FunctionSymbol> getFunctionSymbolsPRNoHead() {
        if (this.functionSymbolsPRNoHead == null) {
            this.computeHeadSignatures();
        }
        return this.functionSymbolsPRNoHead;
    }



    private void computeHeadSignatures() {
        synchronized(this) {
            if (this.headSymbols == null) {
                Set<FunctionSymbol> forbidden = new LinkedHashSet<FunctionSymbol>(this.rAnalysis.getFunctionSymbols());
                Set<FunctionSymbol> headSyms = new LinkedHashSet<FunctionSymbol>();
                // headSyms and forbidden are disjoint!
                // in the end, headSyms should contain the head syms of P,GeneralizedRule
                // and forbidden is the remaining signature of P \cup GeneralizedRule

                for (GeneralizedRule dp : this.pAnalysis.getRules()) {
                    TRSFunctionApplication s = dp.getLeft();

                    // add non-root signature of s to forbidden
                    for (TRSTerm arg : s.getArguments()) {
                        for (FunctionSymbol f : arg.getFunctionSymbols()) {
                            if (forbidden.add(f)) {
                                headSyms.remove(f);
                            }
                        }
                    }

                    // add non-root signature of t to forbidden
                    TRSTerm t = dp.getRight();
                    if (!t.isVariable()) {
                        TRSFunctionApplication tt = (TRSFunctionApplication) t;
                        for (TRSTerm arg : tt.getArguments()) {
                            for (FunctionSymbol f : arg.getFunctionSymbols()) {
                                if (forbidden.add(f)) {
                                    headSyms.remove(f);
                                }
                            }
                        }

                        // add root-symbol of t
                        FunctionSymbol f = tt.getRootSymbol();
                        if (!forbidden.contains(f)) {
                            headSyms.add(f);
                        }
                    }

                    // add root-symbol of s
                    FunctionSymbol f = s.getRootSymbol();
                    if (!forbidden.contains(f)) {
                        headSyms.add(f);
                    }
                }

                forbidden.addAll(headSyms); // now forbidden = signature (P u GeneralizedRule)

                Set<FunctionSymbol> fullSignature = new LinkedHashSet<FunctionSymbol>(forbidden);
                fullSignature.addAll(this.getQ().getExplicitSignature());
                // and fullSignature = signature (P u GeneralizedRule u Q)

                this.functionSymbolsPRNoHead = ImmutableCreator.create(forbidden);
                this.headSymbols = ImmutableCreator.create(headSyms);
                // this.signature = ImmutableCreator.create(fullSignature);
            }
        }
    }

    /**
     * @return the RuleAnalysis<GeneralizedRule> of the p rules
     */
    public RuleAnalysis<GeneralizedRule> getPAnalysis() {
        return this.pAnalysis;
    }

    /**
     * @return the RuleAnalysis<GeneralizedRule> of the r rules
     */
    public RuleAnalysis<GeneralizedRule> getRAnalysis() {
        return this.rAnalysis;
    }

    /**
     * Checks if unrestricted integers occur in the rules.
     */
    public boolean hasUnrestrictedInt() {
        return this.pAnalysis.hasUnrestrictedInt() || this.rAnalysis.hasUnrestrictedInt();
    }

    /**
     * Checks if restricted integers occur in the rules.
     */
    public boolean hasRestrictedInt() {
        return this.pAnalysis.hasRestrictedInt() || this.rAnalysis.hasRestrictedInt();
    }

    /**
     * @param an IUsableRulesEstimation.Estimations
     * @return usable rules computed by a specific estimation
     */
    public IdpQUsableRules getUseableRules(IUsableRulesEstimation.Estimations estimation) {
        if (estimation == null) {
            estimation = IUsableRulesEstimation.Estimations.getDefaultEstimation();
        }
        if (! this.useableRules.containsKey(estimation)) {
            synchronized (this.useableRules) {
                if (! this.useableRules.containsKey(estimation)) {
                    IdpQUsableRules usable = IUsableRulesEstimation.Estimations.getEstimation(this, estimation).getUsableRules(this);
                    this.useableRules.put(estimation, usable);
                    return usable;
                }
            }
        }
        return this.useableRules.get(estimation);
    }

    public IDPPredefinedMap getPreDefinedMap() {
        return this.predefinedMap;
    }

    /**
     * @param an IUsableRulesEstimation.Estimations
     * @return usable rules computed by a specific estimation
     */
    public IUsableRulesEstimation getUseableRulesEstimation(IUsableRulesEstimation.Estimations estimation) {
        if (estimation == null) {
            estimation = IUsableRulesEstimation.Estimations.getDefaultEstimation();
        }
        return IUsableRulesEstimation.Estimations.getEstimation(this, estimation);
    }

    /**
     * Checks if bitwise operations occur in the rules.
     */
    public boolean hasBitwiseOps() {
        return this.pAnalysis.hasBitwiseOps() || this.rAnalysis.hasBitwiseOps();
    }

    /**
     * Checks if defined predefined symbols (sic!) occur in the rules.
     */
    public boolean hasPredefinedDefSymbols() {
        return this.pAnalysis.hasPredefinedDefSymbols() || this.rAnalysis.hasPredefinedDefSymbols();
    }

    /**
     * get R and P as a mapping from defined symbols to corresponding rules
     */
    public ImmutableMap<FunctionSymbol, ImmutableSet<GeneralizedRule>> getRuleMap() {
        if (this.ruleMap == null) {
            synchronized(this) {
                if (this.ruleMap == null) {
                    Map<FunctionSymbol, ImmutableSet<GeneralizedRule>> tmp = new LinkedHashMap<FunctionSymbol, ImmutableSet<GeneralizedRule>> (this.getRAnalysis().getRuleMap());
                    tmp.putAll(this.getPAnalysis().getRuleMap());
                    return this.ruleMap = ImmutableCreator.create(tmp);
                }
            }
        }
        return this.ruleMap;
    }

    /**
     * get R and P
     */
    public ImmutableSet<GeneralizedRule> getRules() {
        if (this.rules == null) {
            synchronized(this) {
                if (this.rules == null) {
                    Set<GeneralizedRule> tmp = new LinkedHashSet<GeneralizedRule> (this.getRAnalysis().getRules());
                    tmp.addAll(this.getPAnalysis().getRules());
                    return this.rules = ImmutableCreator.create(tmp);
                }
            }
        }
        return this.rules;
    }

    public IDPRuleAnalysis change(RuleAnalysis<GeneralizedRule> rAnalysis, RuleAnalysis<GeneralizedRule> pAnalysis, IQTermSet newQ) {
        if ((rAnalysis == null || rAnalysis == this.rAnalysis) &&
                (pAnalysis == null || pAnalysis == this.pAnalysis) &&
                (newQ == null || newQ.equals(this.Q))) {
            return this;
        } else {
            IDPRuleAnalysis res = new IDPRuleAnalysis(rAnalysis != null ? rAnalysis : this.rAnalysis,
                    pAnalysis != null ? pAnalysis : this.pAnalysis,
                    newQ != null ? newQ : this.Q,
                    null);
            if ((rAnalysis == null || rAnalysis == this.rAnalysis) &&
                (pAnalysis == null || pAnalysis == this.pAnalysis))
            {
                synchronized(this) {
                    res.domains = this.domains;
                    res.functionSymbols = this.functionSymbols;
                    res.definedSymbols = this.definedSymbols;
                    res.leftHandSides = this.leftHandSides;
                }
            }
            if ((rAnalysis == null || rAnalysis == this.rAnalysis) &&
                (newQ == null || newQ.equals(this.Q))) {
                synchronized(this) {
                    res.NfQSubsetEqNfR = this.NfQSubsetEqNfR;
                }
            }
            return res;
        }
    }

    public IDPRuleAnalysis changeQ(IQTermSet newQ) {
        IDPRuleAnalysis res = new IDPRuleAnalysis(this.rAnalysis, this.pAnalysis, newQ, null);
        synchronized(this) {
            res.domains = this.domains;
            res.functionSymbols = this.functionSymbols;
            res.definedSymbols = this.definedSymbols;
            res.leftHandSides = this.leftHandSides;
        }
        return res;
    }

    public IDPRuleAnalysis changeP(RuleAnalysis<GeneralizedRule> newPAnalysis) {
        IDPRuleAnalysis res = new IDPRuleAnalysis(this.rAnalysis, newPAnalysis, this.Q, null);
        synchronized(this) {
            res.NfQSubsetEqNfR = this.NfQSubsetEqNfR;
        }
        return res;
    }

    /**
     * Checks if the rules satisfy the variable condition.
     */
    public boolean satVarCondition() {
        return this.rAnalysis.satVarCondition() && this.pAnalysis.satVarCondition();
    }
}
