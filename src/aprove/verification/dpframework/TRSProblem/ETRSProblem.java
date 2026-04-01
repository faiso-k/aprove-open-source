/*
 * Created on 12.01.2006
 */
package aprove.verification.dpframework.TRSProblem;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.runtime.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Unification.Equational.Utility.*;
import aprove.verification.dpframework.BasicStructures.Utility.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Output.*;
import aprove.xml.*;
import immutables.*;

/**
 * An ETRS is a TRS as a set of Rules together with some Equations as a set of Equations.
 *
 * @author stein
 * @version $Id$
 */

public final class ETRSProblem extends DefaultBasicObligation implements Immutable, HTML_Able, ExternUsable {

    private final ImmutableSet<Rule> R;
    private final ImmutableSet<Equation> E;

    // cached / calculated values
     private final int hashCode;
     private volatile Boolean isACandA; //true iff E only contains AC and A Equations
     private volatile Boolean isACandAandC; //true iff E only contains AC, A and C Equations
     private volatile Boolean isC; //true iff E only contains C Equations
     private volatile ImmutableSet<FunctionSymbol> defSymbolsOfR; // defined symbols of R
     private volatile ImmutableSet<FunctionSymbol> signature;        // signature of R and E
     private volatile ImmutableMap<FunctionSymbol, ImmutableSet<Rule>> ruleMap; //mapping from defined symbols to corresponding rules
     private volatile ImmutableMap<FunctionSymbol, ImmutableSet<Equation>> equationMap; //mapping from root symbols of lhs or rhs of an equation to equation
     private volatile ImmutableSet<Rule> extR; // AC Extension of R
     private volatile ImmutableSet<Rule> extendedRules; // extended rules without R;
     private volatile ImmutableSet<Rule> dps;        // the dps of extR
     private volatile ImmutableSet<Rule> edps;        // the dps of E - # E
     private volatile ImmutableMap<FunctionSymbol, FunctionSymbol> defToTup; // defined to tuple-symbol map 
     private volatile ImmutableSet<Equation> eSharp;     // Equations for outer tuple symbols of dps
     private final EUsableRules eUsableRules; //for computing the UsableRules
     private final ESharpUsableEquations eSharpUsableEquations; //for computing the usable Equations of eSharp
     private volatile ImmutableSet<FunctionSymbol> aCandASymbols; //AC and A Symbols of E
     private volatile ImmutableSet<FunctionSymbol> cSymbols; //C Symbols of E
     private volatile ImmutableSet<FunctionSymbol> aCSymbols; //AC Symbols of E
     private volatile ImmutableSet<FunctionSymbol> aSymbols; //A Symbols of E




    /**
     * creates an ETRS problem.
     * @param R - the TRS
     * @param E - the Equations
     */
    private ETRSProblem(final ImmutableSet<Rule> R, final ImmutableSet<Equation> E) {
        super("ETRS", "ETRS");
        this.R = R;
        this.E = E;
        this.isACandAandC = null;
        this.isACandA = null;
        this.isC = null;
        this.defSymbolsOfR = null;
        this.ruleMap = null;
        this.equationMap = null;
        this.aCandASymbols = null;
        this.cSymbols = null;
        this.aCSymbols = null;
        this.aSymbols = null;

        this.hashCode = R.hashCode()*849033+E.hashCode()*84903+8490213;
        this.eUsableRules = new EUsableRules(this);
        this.eSharpUsableEquations = new ESharpUsableEquations(this);
    }

    /**
     * creates a new TRS-Problem for the given collection of Rules,
     * E will be empty
     */
    public static ETRSProblem create(final ImmutableSet<Rule> R) {
        return ETRSProblem.create(R, ImmutableCreator.create(java.util.Collections.<Equation>emptySet()));
    }

    /**
     * creates a new TRS-Problem for the given collection of Rules for R and E
     */
    public static ETRSProblem create(final ImmutableSet<Rule> R, final ImmutableSet<Equation> E) {
        return new ETRSProblem(R, E);
    }

    /**
     * returns DP(E) - # E.
     */
    public ImmutableSet<Rule> getEDPs() {
        this.getDPs(); // ensures, that edps will be computed
        return this.edps;
    }
    
    /**
     * returns the set of DPs of extR, for AC and ACnC case
     */
    public ImmutableSet<Rule> getDPs() {
        if(this.extR == null) {
            this.calculateExtR();
        }

        if (this.dps == null) {
            synchronized(this) {
                if (this.dps == null) {
                    final Set<Rule> dps = new LinkedHashSet<Rule>();
                    final Set<Rule> edps = new LinkedHashSet<Rule>();
                    final Set<FunctionSymbol> signature = new LinkedHashSet<FunctionSymbol>(this.getSignature());
                    final Set<FunctionSymbol> defs = this.getDefinedSymbolsOfR();
                    //Mapping from definedSymbols to uppercase TupleSymbols
                    Map<FunctionSymbol, FunctionSymbol> defToTup = new HashMap<FunctionSymbol, FunctionSymbol>();                                       

                    for (final Rule rule : this.extR) {
                        final Set<TRSFunctionApplication> dpRhss = new LinkedHashSet<TRSFunctionApplication>();
                        final TRSFunctionApplication lhs = rule.getLeft();
                        final TRSTerm rhs = rule.getRight();
                        // get all subterms of rhs of actRule which have a defined symbol as root
                        for(final TRSFunctionApplication subterm : rhs.getNonVariableSubTerms()) {
                            final FunctionSymbol actFuncSym = subterm.getRootSymbol();
                            if(defs.contains(actFuncSym)) {
                                if (!lhs.hasProperSubterm(subterm)) {
                                    dpRhss.add(subterm);
                                }
                            }
                        }

                        if (dpRhss.isEmpty()) {
                            continue;
                        }

                        final FunctionSymbol tf = ETRSProblem.getTupleSymbol(lhs.getRootSymbol(), defToTup, signature);
                        final TRSFunctionApplication tlhs = TRSTerm.createFunctionApplication(tf, lhs.getArguments());

                        for (final TRSFunctionApplication dpRhs : dpRhss) {
                            final FunctionSymbol tg = ETRSProblem.getTupleSymbol(dpRhs.getRootSymbol(), defToTup, signature);
                            final TRSFunctionApplication trhs = TRSTerm.createFunctionApplication(tg, dpRhs.getArguments());
                            dps.add(Rule.create(tlhs, trhs));
                        }

                    }
                    
                    
                	    for (Equation e : this.getE()) {
                		TRSFunctionApplication l = (TRSFunctionApplication) e.getLeft();
                		TRSFunctionApplication r = (TRSFunctionApplication) e.getRight();
                		FunctionSymbol f = l.getRootSymbol();
                		if (defs.contains(f) && e.checkAEquation()) {
                		    FunctionSymbol tf = ETRSProblem.getTupleSymbol(l.getRootSymbol(), defToTup, signature);
                		    TRSFunctionApplication tlhs = TRSTerm.createFunctionApplication(tf, l.getArguments());
                		    TRSFunctionApplication trhs = TRSTerm.createFunctionApplication(tf, 
                			    ((TRSFunctionApplication) r.getArgument(1)).getArguments());
                		    edps.add(Rule.create(tlhs, trhs));
                		}
                	    }

                    this.dps = ImmutableCreator.create(dps);
                    this.edps = ImmutableCreator.create(edps);
                    this.defToTup = ImmutableCreator.create(defToTup);
                    this.calculateESharp(defToTup);
                }
            }
        }
        return this.dps;
    }
    
    public ImmutableMap<FunctionSymbol, FunctionSymbol> getDefToTupMap() {
	if (this.defToTup != null) {
	    this.getDPs();
	}
	return this.defToTup;
    }

    /**
     * Returns the signature of R and E.
     */
    public synchronized ImmutableSet<FunctionSymbol> getSignature() {
        if (this.signature == null) {
            final Set<FunctionSymbol> signature = CollectionUtils.getFunctionSymbols(this.R);
            signature.addAll(CollectionUtils.getFunctionSymbols(this.E));
            this.signature = ImmutableCreator.create(signature);
        }
        return this.signature;
    }

    /**
     * Returns the signature of R.
     */
    public synchronized ImmutableSet<FunctionSymbol> getSignatureOfR() {
        if (this.signature == null) {
            final Set<FunctionSymbol> signature = CollectionUtils.getFunctionSymbols(this.R);
            this.signature = ImmutableCreator.create(signature);
        }
        return this.signature;
    }

    /**
     * looksup a tuple symbol for a defined symbol f. If it is not already defined, a new symbol is created (which is not
     * contained in allSyms) and the mapping is stored, and the new symbol is added to allSyms
     */
    private static FunctionSymbol getTupleSymbol(final FunctionSymbol f, final Map<FunctionSymbol, FunctionSymbol> defToTup, final Set<FunctionSymbol> allSyms) {
        FunctionSymbol tf = defToTup.get(f);
        if (tf == null) {
            final String wishedName = f.getName().toUpperCase();
            final int arity = f.getArity();
            int nr = 1;
            tf = FunctionSymbol.create(wishedName, arity);
            while (!allSyms.add(tf)) {
                tf = FunctionSymbol.create(wishedName+"^"+nr, arity);
                nr++;
            }

            defToTup.put(f, tf);
        }
        return tf;
    }

    /**
     * Calculates the Extension of R w.r.t. AC or (AC and C) Theory E.
     * So for now A Symbols are treated as AC Symbols for the Extension.
     */
    private synchronized void calculateExtR() {
        if(Globals.useAssertions) {
            assert this.checkIdenticalUniqueVariablesForE()
                  && this.checkNonCollapsingForE()
                  && this.checkACandAandC();
        }

        final LinkedHashSet<Rule> extR = new LinkedHashSet<Rule>();
        
        if(!this.getE().isEmpty()) {
            if(Globals.useAssertions) {
                assert this.checkACandAandC();
            }

            FreshVarGenerator varGen;
            final Set<FunctionSymbol> ACs = this.getACandASymbols();
            final Set<FunctionSymbol> Cs = this.getCSymbols();
            for(final FunctionSymbol f : ACs) {
                final Set<Rule> fRules = this.getRuleMap().get(f);
                if (fRules != null) {
                    for(final Rule rule : fRules) {
                        varGen = new FreshVarGenerator(rule.getVariables());
                        final TRSVariable var = varGen.getFreshVariable(TRSTerm.createVariable("ext"), false);
                        if(Options.certifier.isCpf() || !this.noACExtensionNeeded(rule, ACs)) {
                            ArrayList<TRSTerm> args = new ArrayList<TRSTerm>();
                            args.add(rule.getLeft());
                            args.add(var);
                            final TRSTerm l = TRSTerm.createFunctionApplication(f, ImmutableCreator.create(args));
                            args = new ArrayList<TRSTerm>();
                            args.add(rule.getRight());
                            args.add(var);
                            final TRSTerm r = TRSTerm.createFunctionApplication(f, ImmutableCreator.create(args));
                            final Rule newRule = Rule.create((TRSFunctionApplication)l, r);
                            if(Options.certifier.isCpf() || !this.hasEquivalentRule(newRule, fRules, ACs, Cs)) {
                                extR.add(newRule);
                            }
                        }
                    }
                }
            }            
        }
        this.extendedRules = ImmutableCreator.create(extR);
        final Set<Rule> extR_R = new LinkedHashSet<>(this.getR());
        extR_R.addAll(this.extendedRules);
        this.extR = ImmutableCreator.create(extR_R);

        if(Globals.DEBUG_STEIN) {
            System.out.println("extR calculated:");
            System.out.println(extR.toString());
        }
    }

    /**
     * Returns true iff no AC Extension is needed for the given rule.
     * Helper function for private void getExt(ETRSProblem rWithE)
     */
    private boolean noACExtensionNeeded(final Rule rule, final Set<FunctionSymbol> ACs) {
        final TRSTerm l = rule.getLeft();
        final TRSTerm r = rule.getRight();
        boolean res = false;
        final Set<TRSVariable> lCand = ACTerm.create(l, ACs).getLinearImmediateVars();
        if(r.isVariable()) {
            res = lCand.contains(r);
        }
        else {
            if( (l instanceof TRSFunctionApplication && r instanceof TRSFunctionApplication) &&
                    ((TRSFunctionApplication)l).getRootSymbol().equals(((TRSFunctionApplication)r).getRootSymbol()) ) {
                final Set<TRSVariable> rCand = ACTerm.create(r, ACs).getLinearImmediateVars();
                rCand.retainAll(lCand);
                res = !rCand.isEmpty();
            }
        }
        return res;
    }

    /**
     * Returns true iff an AC/C equivalent rule of the given newRule occurs in rules.
     * Helper function for private void getExt(ETRSProblem rWithE)
     */
    private boolean hasEquivalentRule(final Rule newRule, final Set<Rule> rules, final Set<FunctionSymbol> ACs, final Set<FunctionSymbol> Cs) {
        for(final Rule testR : rules) {
            if(ACnCTerm.create(testR.getLeft(), ACs, Cs).equals(ACnCTerm.create(newRule.getLeft(), ACs, Cs)) &&
               ACnCTerm.create(testR.getRight(), ACs, Cs).equals(ACnCTerm.create(newRule.getRight(), ACs, Cs))) {
                return true;
            }
        }
        return false;
    }

    /**
     * Calculates eSharp with the given map from FunctionSymbols of R to FunctionSymbols of P.
     */

    private void calculateESharp(final Map<FunctionSymbol, FunctionSymbol> defToTup) {
        if(this.dps == null) {
            this.getDPs();
        }
        if(Globals.useAssertions) {
            assert this.checkACandAandC();
        }
        final Set<Equation> eSharp = new LinkedHashSet<Equation>();
        for(final Equation e : this.E) {
            if(e.getLeft() instanceof TRSFunctionApplication) {
                final TRSFunctionApplication lhs = (TRSFunctionApplication)e.getLeft();
                final FunctionSymbol F = defToTup.get(lhs.getRootSymbol());
                if(F != null) {
                    final TRSTerm newLhs = TRSTerm.createFunctionApplication(F, lhs.getArguments());
                    final TRSTerm newRhs = TRSTerm.createFunctionApplication(F, ((TRSFunctionApplication)e.getRight()).getArguments());
                    final Equation newEq = Equation.create(newLhs,newRhs);
                    eSharp.add(newEq);
                }
            }
        }
        this.eSharp = ImmutableCreator.create(eSharp);
    }

    /**
     * Calculates eSharp as the Equations for the dps, in AC/C case.
     */
    public synchronized ImmutableSet<Equation> getESharp() {
        if(this.eSharp == null) {
            this.getDPs();
        }
        return this.eSharp;
    }

    @Override
    public boolean equals(final Object oth) {
        if (this == oth) {
            return true;
        }

        if (oth == null) {
            return false;
        }

        if (oth.getClass() != this.getClass()) {
            return false;
        }

        final ETRSProblem other = (ETRSProblem) oth;
        if (!this.R.equals(other.R)) {
            return false;
        }

        return this.E.equals(other.E);
    }

    private void calculateDefSymbolsAndRuleMap() {
        final Map<FunctionSymbol, Set<Rule>> ruleMap = new LinkedHashMap<FunctionSymbol, Set<Rule>>();
        for (final Rule rule : this.R) {
            final FunctionSymbol f = rule.getRootSymbol();
            Set<Rule> fRules = ruleMap.get(f);
            if (fRules == null) {
                fRules = new LinkedHashSet<Rule>();
                ruleMap.put(f, fRules);
            }
            fRules.add(rule);
        }
        // make immutable
        final Map<FunctionSymbol, ImmutableSet<Rule>> immutableMap = new LinkedHashMap<FunctionSymbol, ImmutableSet<Rule>>();
        for (final Map.Entry<FunctionSymbol, Set<Rule>> entry : ruleMap.entrySet()) {
            immutableMap.put(entry.getKey(), ImmutableCreator.create(entry.getValue()));
        }
        this.ruleMap = ImmutableCreator.create(immutableMap);
        this.defSymbolsOfR = ImmutableCreator.create(immutableMap.keySet());
    }

    private void calculateEquationMap() {
        final Map<FunctionSymbol, Set<Equation>> equationMap = new LinkedHashMap<FunctionSymbol, Set<Equation>>();
        for(final Equation eq:this.E) {
            for(final FunctionSymbol f : eq.getRootSymbols()) {
                Set<Equation> fEquation = equationMap.get(f);
                if(fEquation == null) {
                    fEquation = new LinkedHashSet<Equation>();
                    equationMap.put(f, fEquation);
                }
                fEquation.add(eq);
            }
        }
        //make immutable
        final Map<FunctionSymbol, ImmutableSet<Equation>> immutableMap = new LinkedHashMap<FunctionSymbol, ImmutableSet<Equation>>();
        for (final Map.Entry<FunctionSymbol, Set<Equation>> entry : equationMap.entrySet()) {
            immutableMap.put(entry.getKey(), ImmutableCreator.create(entry.getValue()));
        }
        this.equationMap = ImmutableCreator.create(immutableMap);
    }

    private void calculateIsACandAandC() {
        this.isACandAandC = true;
        for(final Equation eq : this.E) {
            if( !eq.checkCEquation() && !eq.checkAEquation() ) {
                this.isACandAandC = false;
                break;
            }
        }
    }

    private void calculateIsACandA() {
        this.isACandA = true;
        for(final Equation eq : this.E) {
            if(eq.getLeft() instanceof TRSFunctionApplication) {
                final FunctionSymbol f = ((TRSFunctionApplication)eq.getLeft()).getRootSymbol();
                final Equation aEquation = Equation.createAEquation(f);

                if( !(eq.checkCEquation() && this.E.contains(aEquation)) && !eq.checkAEquation() ) {
                    this.isACandA = false;
                    break;
                }
            }
            else
            {
                this.isACandA = false;
                break;
            }
        }
    }

    private void calculateIsC() {
        this.isC = true;
        for(final Equation eq : this.E) {
            if( !eq.checkCEquation()) {
                this.isC = false;
                break;
            }
        }
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

    /**
     * returns true iff all equations have identical variables.
     */
    public boolean checkIdenticalVariablesForE() {
        for(final Equation e : this.E) {
            if(!e.checkIdenticalVariables()) {
                return false;
            }
        }
        return true;
    }

    /**
     * returns true iff all equations have unique variables.
     */
    public boolean checkUniqueVariablesForE() {
        for(final Equation e : this.E) {
            if(!e.checkIdenticalVariables()) {
                return false;
            }
        }
        return true;
    }

    /**
     * returns true iff all equations have identical unique variables.
     */
    public boolean checkIdenticalUniqueVariablesForE() {
        for(final Equation e : this.E) {
            if(!e.checkIdenticalUniqueVariables()) {
                return false;
            }
        }
        return true;
    }

    /**
     * returns true iff all equations are non collapsing.
     */
    public boolean checkNonCollapsingForE() {
        for(final Equation e : this.E) {
            if(!e.checkNonCollapsing()) {
                return false;
            }
        }
        return true;
    }

    /**
     * returns true iff E only contains AC, A and C Equations, e.g. if E is an (AC \cup A \cup C)- Theory.
     * especially returns true if checkACandA returns true
     */
    public synchronized boolean checkACandAandC() {
        if(this.isACandAandC == null) {
            this.calculateIsACandAandC();
        }
        return this.isACandAandC;
    }

    /**
     * returns true iff E only contains AC and A Equations, e.g. if E is an (AC \cup A)-Theory
     */
    public synchronized boolean checkACandA() {
        if(this.isACandA == null) {
            this.calculateIsACandA();
        }
        return this.isACandA;
    }

    /**
     * returns true iff E only contains C Equations, e.g. if E is an C-Theory
     */
    public synchronized boolean checkC() {
        if(this.isC == null) {
            this.calculateIsC();
        }
        return this.isC;
    }

    /**
     * returns the set of AC- and A-Symbols of E iff E is (AC \cup C \cup A)-Theory
     * else the empty set
     */
    public synchronized ImmutableSet<FunctionSymbol> getACandASymbols() {
        if(this.aCandASymbols == null) {
            this.getDefinedSymbolsOfR();
            final LinkedHashSet<FunctionSymbol> aCSymbols = new LinkedHashSet<FunctionSymbol>();
            if(this.checkACandAandC()) {
                for(final Equation eq : this.E) {
                    final FunctionSymbol f = ((TRSFunctionApplication)eq.getLeft()).getRootSymbol();
                    final Equation aEquation = Equation.createAEquation(f);

                    if( (eq.checkCEquation() && this.E.contains(aEquation)) || eq.checkAEquation() ) {
                        aCSymbols.add(f);
                    }
                }
                this.aCandASymbols = ImmutableCreator.create(aCSymbols);
            }
        }
        return this.aCandASymbols;
    }

    /**
     * returns the set of AC-Symbols of E iff E is (AC \cup C \cup A)-Theory
     * else the empty set
     */
    public synchronized ImmutableSet<FunctionSymbol> getACSymbols() {
        if(this.aCSymbols == null) {
            this.getDefinedSymbolsOfR();
            final LinkedHashSet<FunctionSymbol> symbols = new LinkedHashSet<FunctionSymbol>();
            if(this.checkACandAandC()) {
                for(final Equation eq : this.E) {
                    final FunctionSymbol f = ((TRSFunctionApplication)eq.getLeft()).getRootSymbol();
                    final Equation cEquation = Equation.createCEquation(f);
                    final Equation aEquation = Equation.createAEquation(f);
                    if( this.E.contains(cEquation) && this.E.contains(aEquation)) {
                            symbols.add(f);
                    }
                }
            }
            this.aCSymbols = ImmutableCreator.create(symbols);
        }
        return this.aCSymbols;
    }

    /**
     * returns the set of A-Symbols of E iff E is (AC \cup C \cup A)-Theory
     * else the empty set
     */
    public synchronized ImmutableSet<FunctionSymbol> getASymbols() {
        if(this.aSymbols == null) {
            this.getDefinedSymbolsOfR();
            final LinkedHashSet<FunctionSymbol> symbols = new LinkedHashSet<FunctionSymbol>();
            if(this.checkACandAandC()) {
                for(final Equation eq : this.E) {
                    final FunctionSymbol f = ((TRSFunctionApplication)eq.getLeft()).getRootSymbol();
                    final Equation cEquation = Equation.createCEquation(f);
                    final Equation aEquation = Equation.createAEquation(f);
                    if( !this.E.contains(cEquation) && this.E.contains(aEquation)) {
                            symbols.add(f);
                    }

                }
            }
            this.aSymbols = ImmutableCreator.create(symbols);
        }
        return this.aSymbols;
    }

    /**
     * returns the set of C Symbols of E iff E is (AC or C or A) Theory
     * else the empty set
     */
    public synchronized ImmutableSet<FunctionSymbol> getCSymbols() {
        if(this.cSymbols == null) {
            this.getDefinedSymbolsOfR();
            final LinkedHashSet<FunctionSymbol> symbols = new LinkedHashSet<FunctionSymbol>();
            if(this.checkACandAandC()) {
                for(final Equation eq : this.E) {
                    final FunctionSymbol f = ((TRSFunctionApplication)eq.getLeft()).getRootSymbol();
                    final Equation cEquation = Equation.createCEquation(f);
                    final Equation aEquation = Equation.createAEquation(f);
                    if( this.E.contains(cEquation) && !this.E.contains(aEquation)) {
                            symbols.add(f);
                    }
                }
            }
            this.cSymbols = ImmutableCreator.create(symbols);
        }
        return this.cSymbols;
    }


    public ImmutableSet<Rule> getR() {
        return this.R;
    }

    public synchronized ImmutableSet<Rule> getExtR() {
        if(this.extR==null) {
            this.calculateExtR();
        }
        return this.extR;
    }

    public synchronized ImmutableSet<Rule> getExtendedRules() {
        if(this.extR==null) {
            this.calculateExtR();
        }
        return this.extendedRules;
    }

    public ImmutableSet<Equation> getE() {
        return this.E;
    }

    public EUsableRules getEUsableRulesCalculator() {
        return this.eUsableRules;
    }

    public ESharpUsableEquations getESharpUsableEquationsCalculator() {
        return this.eSharpUsableEquations;
    }

    /**
     * returns the set of terms in R and E,
     * the set may be modified
     */
    public Set<TRSTerm> getTerms() {
        // terms of R
        final Set<TRSTerm> terms = CollectionUtils.getTerms(this.R);
        // plus terms of E
        terms.addAll(CollectionUtils.getTerms(this.E));
        return terms;
    }

    /**
     * creates a sub problem with less rules in R
     * @param rules
     * @return
     */
    public ETRSProblem createSubProblemWithSmallerR(final ImmutableSet<Rule> rules) {
        if (Globals.useAssertions) {
            assert(this.R.containsAll(rules));
        }
        if (this.R.size() == rules.size()) {
            if (Globals.DEBUG_STEIN) {
                System.out.println("Warning: createSubProblem in QTRS produces identity");
            }
            return this;
        }

        return new ETRSProblem(rules, this.E);
    }

    /**
     * creates a sub problem with less eqns in E
     */
    public ETRSProblem createSubProblemWithSmallerE(final ImmutableSet<Equation> eqns) {
        if (Globals.useAssertions) {
            assert(this.E.containsAll(eqns));
        }
        if (this.E.size() == eqns.size()) {
            if (Globals.DEBUG_STEIN) {
                System.out.println("Warning: createSubProblem in QTRS produces identity");
            }
            return this;
        }

        return new ETRSProblem(this.R, eqns);
    }

    public ImmutableSet<FunctionSymbol> getDefinedSymbolsOfR() {
        if (this.defSymbolsOfR == null) {
            this.calculateDefSymbolsAndRuleMap();
        }
        return this.defSymbolsOfR;
    }

    /**
     * get R as a mapping from defined symbols to corresponding rules
     */
    public ImmutableMap<FunctionSymbol, ImmutableSet<Rule>> getRuleMap() {
        if (this.ruleMap == null) {
            synchronized(this) {
                if (this.ruleMap == null) {
                    this.calculateDefSymbolsAndRuleMap();
                }
            }
        }
        return this.ruleMap;
    }

    /**
     * get E as Map from FunctionSymbols to Equations with this FunctionSymbol as a root
     */
    public synchronized ImmutableMap<FunctionSymbol, ImmutableSet<Equation>> getEquationMap() {
        if(this.equationMap == null) {
            this.calculateEquationMap();
        }
        return this.equationMap;
    }

    public String getName() {
        return "Equational TRS";
    }

    /**
     * Returns set of terms E_C-equivalent to t,
     * where E_C are the C-equations of E
     */
    public Set<TRSTerm> getCEquivalent(final TRSTerm t){
        final Set<TRSTerm> ret = new LinkedHashSet<TRSTerm>();
        if(t.isVariable()) {
            ret.add(t);
        }
        else {
            final TRSFunctionApplication fa = (TRSFunctionApplication)t;
            final FunctionSymbol f = fa.getRootSymbol();
            if(fa.getArguments().size()==0) {
                ret.add(t);
                return ret;
            }
            if(this.getCSymbols().contains(f)) {
                for(final TRSTerm t_1:this.getCEquivalent(fa.getArgument(0))) {
                    for(final TRSTerm t_2:this.getCEquivalent(fa.getArgument(1))) {
                        ret.add(TRSTerm.createFunctionApplication(f,Equation.createArgArrayList(Arrays.asList(t_1,t_2))));
                        ret.add(TRSTerm.createFunctionApplication(f,Equation.createArgArrayList(Arrays.asList(t_2,t_1))));
                    }
                }
            }
            else {
                final List<Set<TRSTerm>> equivList = new ArrayList<Set<TRSTerm>>();
                for(final TRSTerm arg:fa.getArguments()) {
                    equivList.add(this.getCEquivalent(arg));
                }
                for(final ArrayList<TRSTerm> args:this.getArgPermutations(equivList)) {
                    ret.add(TRSTerm.createFunctionApplication(f,ImmutableCreator.create(args)));
                }

            }
        }

        return ret;
    }

    private Set<ArrayList<TRSTerm>> getArgPermutations(final List<Set<TRSTerm>> equivList) {
        final Set<ArrayList<TRSTerm>> ret = new LinkedHashSet<ArrayList<TRSTerm>>();

        if(equivList.size()>0) {
            final List<Set<TRSTerm>> remainingList = new ArrayList<Set<TRSTerm>>();
            remainingList.addAll(equivList);
            final Set<TRSTerm> top = remainingList.get(0);
            remainingList.remove(0);

            for(final TRSTerm t:top) {
                if(remainingList.isEmpty()) {
                    final ArrayList<TRSTerm> argList = new ArrayList<TRSTerm>();
                    argList.add(t);
                    ret.add(argList);
                }
                else {
                    for(final ArrayList<TRSTerm> rem:this.getArgPermutations(remainingList)) {
                        final ArrayList<TRSTerm> argList = new ArrayList<TRSTerm>();
                        argList.add(t);
                        argList.addAll(rem);
                        ret.add(argList);
                    }
                }
            }
        }

        return ret;
    }

    @Override
    public String export(final Export_Util o) {
        final StringBuffer s = new StringBuffer();
        s.append(o.export("Equational rewrite system:"));
        s.append(o.cond_linebreak());
        if (this.R.isEmpty()) {
            s.append("R is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("The TRS R consists of the following rules:"));
            s.append(o.cond_linebreak());
            s.append(o.set(this.R, Export_Util.RULES));
            s.append(o.cond_linebreak());
        }

        if (this.E.isEmpty()) {
            s.append("E is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("The set E consists of the following equations:"));
            s.append(o.cond_linebreak());
            s.append(o.set(this.E, Export_Util.RULES));
            s.append(o.cond_linebreak());
        }

        return s.toString();
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {

        final Element etrsTag = XMLTag.ETRS.createElement(doc);
        final Element trsTag = XMLTag.TRS.createElement(doc);
        CollectionUtils.addChildren(this.R, trsTag, doc, xmlMetaData);
        etrsTag.appendChild(trsTag);
        final Element equTag = XMLTag.EQUATIONS.createElement(doc);
        CollectionUtils.addChildren(this.E, equTag, doc, xmlMetaData);
        etrsTag.appendChild(equTag);
        final Element sigTag = XMLTag.SIGNATURE.createElement(doc);
        CollectionUtils.addChildren(this.getSignature(), sigTag, doc, xmlMetaData);
        etrsTag.appendChild(sigTag);
        return etrsTag;
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public String toHTML() {
        return this.export(new HTML_Util());
    }

    @Override
    public String toExternString() {
        final TRSGenerator trsGen =  new TRSGenerator();
        trsGen.writeRules(this.R);
        trsGen.writeEquations(this.E);
        return trsGen.getTRSString(false, null);
    }

    @Override
    public String externName() {
        return "trs";
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new DefaultProofPurposeDescriptor(this, "Termination");
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getStrategyName() {
        return "equ";
    }
    
    @Override
    public Element getCPFInput(final Document doc, final XMLMetaData xmlMetaData, final TruthValue tv) {
        final Element trsInput = CPFTag.AC_REWRITE_SYSTEM.create(doc,
                CPFTag.trs(doc, xmlMetaData, this.getR()));
        
        Element A = CPFTag.A_SYMBOLS.create(doc);
        for (FunctionSymbol f : this.getASymbols()) {
            A.appendChild(f.toCPF(doc, xmlMetaData));
        }
        for (FunctionSymbol f : this.getACandASymbols()) {
            A.appendChild(f.toCPF(doc, xmlMetaData));
        }
        trsInput.appendChild(A);
        
        Element C = CPFTag.C_SYMBOLS.create(doc);
        for (FunctionSymbol f : this.getCSymbols()) {
            C.appendChild(f.toCPF(doc, xmlMetaData));
        }
        for (FunctionSymbol f : this.getACSymbols()) {
            C.appendChild(f.toCPF(doc, xmlMetaData));
        }
        trsInput.appendChild(C);

        return trsInput;
    }

}
