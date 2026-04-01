/*
 * Created on 24.11.2004
 */

/**
 * @author patwie
 * @version $Id$
 */

/**
 * This class implements a new proof obligation,
 * namely a Relative TRS proof obligation.
 */
package aprove.verification.dpframework.TRSProblem;


import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Output.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;



public final class RelTRSProblem extends DefaultBasicObligation implements HTML_Able, HasTRSTerms, ExternUsable{

    private final ImmutableSet<Rule> R;
    private final ImmutableSet<Rule> S;



    // cached / calculated values
    private final int hashCode;
    private final boolean RIntersectedSisEmpty;
    //private MemoryIterable<ImmutableTriple<Term, Term, Boolean>> critPairs;
    private ImmutableSet<FunctionSymbol> signature;        // signature of R and S
    private ImmutableSet<FunctionSymbol> Rsignature;       // signature of R
    private volatile ImmutableSet<FunctionSymbol> defSymbolsOfR;        // the same as ruleMap.keySet();
    private ImmutableSet<FunctionSymbol> Ssignature;       // signature of S
    private volatile ImmutableSet<FunctionSymbol> defSymbolsOfS;        // the same as ruleMap.keySet();
    private volatile ImmutableMap<FunctionSymbol, ImmutableSet<Rule>> ruleMapOfR;
    private volatile ImmutableMap<FunctionSymbol, ImmutableSet<Rule>> reverseRuleMapOfR;
    private volatile ImmutableMap<FunctionSymbol, ImmutableSet<Rule>> ruleMapOfS;
    private volatile ImmutableMap<FunctionSymbol, ImmutableSet<Rule>> reverseRuleMapOfS;
    private ImmutableSet<Rule> lhsWhereRhsIsVariableOfR;
    private ImmutableSet<Rule> lhsWhereRhsIsVariableOfS;
    private final boolean ROverlapping;
    private final boolean SOverlapping;


    /**
     * creates a Rel-TRS problem.
     * @param R - the Rules of the TRS
     * @param S - the Relative Rules of the TRS
     */
    private RelTRSProblem(final ImmutableSet<Rule> R, final ImmutableSet<Rule> S) {
        super("RelTRS", "Relative TRS");
        if(Globals.useAssertions) {
            assert(RelTRSProblem.checkRIntersectSisEmpty(R, S));
        }
        this.RIntersectedSisEmpty = true;
        this.R = R;
        this.S = S;
        this.hashCode = R.hashCode()*849033+S.hashCode()*84903+8490213;
        //this.critPairs = null;
        this.ROverlapping = aprove.verification.dpframework.BasicStructures.CollectionUtils.isOverlapping(R);
        this.SOverlapping = aprove.verification.dpframework.BasicStructures.CollectionUtils.isOverlapping(S);
        this.signature = null;
        this.Rsignature = null;
        this.defSymbolsOfR = null;
        this.Ssignature = null;
        this.defSymbolsOfS = null;
        this.ruleMapOfR = null;
        this.reverseRuleMapOfR = null;
        this.ruleMapOfS = null;
        this.reverseRuleMapOfS = null;
        this.lhsWhereRhsIsVariableOfR = null;
        this.lhsWhereRhsIsVariableOfS = null;
    }
    
    /**
     * creates a Rel-TRS problem with rel-rules that may have vars as lhs.
     * Hence, we replace those rules x -> r by f(x) -> f(r) for every function symbol f.
     * Only allowed for SRSs, i.e., all those f must have an arity of at most 1.
     * TODO: Really only allowed for SRSs? Currently this is allowed for TRSs as well.
     * Additionally, we may remove rules that occur both in R and S from S.
     * @param R - the Rules of the TRS
     * @param S - the Relative Rules of the TRS
     */
    private RelTRSProblem(final ImmutableSet<Rule> R, final ImmutableSet<Rule> S, final ImmutableSet<Pair<TRSTerm, TRSTerm>> lhsVarRules) {
        super("RelTRS", "Relative TRS");
        
        Set<Rule> initialS = new HashSet<Rule>();
        for(Rule r : S) {
            if(!R.contains(r)) {
                initialS.add(r);
            }
        }
        
        Set<FunctionSymbol> currSignature = new HashSet<>();
        currSignature.addAll(CollectionUtils.getFunctionSymbols(R));
        currSignature.addAll(CollectionUtils.getFunctionSymbols(S));

        for(Pair<TRSTerm, TRSTerm> p : lhsVarRules) {
            currSignature.addAll(CollectionUtils.getFunctionSymbols(p.x));
            currSignature.addAll(CollectionUtils.getFunctionSymbols(p.y));
        }
        
        Set<Rule> newS = new HashSet<Rule>();
        newS.addAll(initialS);
        
        for(Pair<TRSTerm, TRSTerm> p : lhsVarRules) {
            
            for(FunctionSymbol f : currSignature) {
                
                final TRSVariable[] xs = new TRSVariable[f.getArity()];
                for (int i = 0; i < f.getArity(); i++) {
                    xs[i] = TRSTerm.createVariable("y_" + (i + 1));
                }
                
                for(int i = 0; i < f.getArity(); i++) {
                    
                    TRSTerm[] argslhs = new TRSTerm[f.getArity()];
                    TRSTerm[] argsrhs = new TRSTerm[f.getArity()];
                    for(int j = 0; j < i; j++) {
                        argslhs[j] = xs[j];
                        argsrhs[j] = xs[j];
                    }
                    argslhs[i] = p.x.getStandardRenumbered();
                    argsrhs[i] = p.y.getStandardRenumbered();
                    for(int j = i + 1; j < f.getArity(); j++) {
                        argslhs[j] = xs[j];
                        argsrhs[j] = xs[j];
                    }
                    
                    TRSFunctionApplication newLHS = TRSTerm.createFunctionApplication(f, argslhs);
                    TRSFunctionApplication newRHS = TRSTerm.createFunctionApplication(f, argsrhs);
                    
                    newS.add(Rule.create(newLHS, newRHS));   
                }
            }
        }
        
        this.RIntersectedSisEmpty = true;
        this.R = R;
        this.S = ImmutableCreator.create(newS);
        this.hashCode = this.R.hashCode()*849033+this.S.hashCode()*84903+8490213;
        this.ROverlapping = aprove.verification.dpframework.BasicStructures.CollectionUtils.isOverlapping(this.R);
        this.SOverlapping = aprove.verification.dpframework.BasicStructures.CollectionUtils.isOverlapping(this.S);
        this.signature = null;
        this.Rsignature = null;
        this.defSymbolsOfR = null;
        this.Ssignature = null;
        this.defSymbolsOfS = null;
        this.ruleMapOfR = null;
        this.reverseRuleMapOfR = null;
        this.ruleMapOfS = null;
        this.reverseRuleMapOfS = null;
        this.lhsWhereRhsIsVariableOfR = null;
        this.lhsWhereRhsIsVariableOfS = null;
    }


    /**
     * creates a new RelTRS-Problem for the given collection of Rules,
     * S will be empty
     * @param R the Rules of the TRS
     */
    public static RelTRSProblem create(final ImmutableSet<Rule> R) {
        return RelTRSProblem.create(R, ImmutableCreator.create(java.util.Collections.<Rule>emptySet()));

    }

    /**
     * creates a new TRS-Problem for the given collection of Rules for R and S
     * @param R the Rules of the TRS
     * @param S the Relative Rules of the TRS
     */
    public static RelTRSProblem create(final ImmutableSet<Rule> R, final ImmutableSet<Rule> S){
        return new RelTRSProblem(R, S);
    }

    /**
     * creates a new TRS-Problem for the given collection of Rules for R and S.
     * Additionally, we handle rules with variables as lhs and may remove rules
     * that occur both in R and S from S.
     * @param R the Rules of the TRS
     * @param S the Relative Rules of the TRS
     */
    public static RelTRSProblem create(final ImmutableSet<Rule> R, final ImmutableSet<Rule> S, final ImmutableSet<Pair<TRSTerm, TRSTerm>> lhsVarRules){
        return new RelTRSProblem(R, S, lhsVarRules);
    }

    /**
     * checks whether R intersected with S is empty
     */
    private static boolean checkRIntersectSisEmpty(final ImmutableSet<Rule> R, final ImmutableSet<Rule> S) {
        for(final Rule rr : R) {
            if(S.contains(rr)) {
                return false;
            }
        }
        return true;
    }

    /**
     * checks whether R union S equals R` union S`
     */
    private static boolean checkUnionCondition(final ImmutableSet<Rule> R, final ImmutableSet<Rule> S,
                                                final ImmutableSet<Rule> PrimeR,  final ImmutableSet<Rule> PrimeS){
        final Set<Rule> union1 = new LinkedHashSet<Rule>();
        final Set<Rule> union2 = new LinkedHashSet<Rule>();
        union1.addAll(R);
        union1.addAll(S);
        union2.addAll(PrimeR);
        union2.addAll(PrimeS);
        return (union1.equals(union2));

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

        final RelTRSProblem other = (RelTRSProblem) oth;
        if (!this.R.equals(other.R)) {
            return false;
        }

        return this.S.equals(other.S);
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

    @Override
    public ObligationType getObligationType() {
        return ObligationType.RELATIVE;
    }

    public ImmutableSet<Rule> getR() {
        return this.R;
    }

    public ImmutableSet<Rule> getS() {
        return this.S;
    }

    public Set<Rule> getRules() {
        int size = R.size() + S.size();
        Set<Rule> res = new LinkedHashSet<Rule>(size);
        res.addAll(R);
        res.addAll(S);
        return res;
    }

    public int getMaxArity() {
        int result = 0;
        for (final FunctionSymbol fsym : this.getSignature()) {
            result = Math.max(result, fsym.getArity());
        }
        return result;
    }
    
    public boolean isDuplicating() {
        return getR().stream().anyMatch(r -> r.isDuplicating())
            || getS().stream().anyMatch(r -> r.isDuplicating());
    }
    
    public boolean isRDuplicating() {
        return getR().stream().anyMatch(r -> r.isDuplicating());
    }
    
    public boolean isSDuplicating() {
        return getS().stream().anyMatch(r -> r.isDuplicating());
    }
    
    public Pair<Pair<Set<Rule>, Set<Rule>>, Map<FunctionSymbol, FunctionSymbol>> getRelativeADPs() {
        
        final Set<FunctionSymbol> signature = new LinkedHashSet<FunctionSymbol>(this.getSignature());
        final Map<FunctionSymbol, FunctionSymbol> annotatorMap = new LinkedHashMap<FunctionSymbol, FunctionSymbol>();
        final Set<FunctionSymbol> defSymbols = new HashSet<FunctionSymbol>();
        defSymbols.addAll(this.getDefinedSymbolsOfR());
        defSymbols.addAll(this.getDefinedSymbolsOfS());

        for (FunctionSymbol fs: defSymbols) {
            QTRSProblem.getTupleSymbol(fs, annotatorMap, signature);
        }

        var res = new Pair<Set<Rule>, Set<Rule>>(
            new LinkedHashSet<Rule>(R.size() * defSymbols.size()),
            new LinkedHashSet<Rule>(S.size() * defSymbols.size() * defSymbols.size())
        );  // TODO: these size estimates don't account for symbol re-use

        for (Rule rule : R) {  // Absolute rules
            final TRSFunctionApplication lhs = rule.getLeft();
            final TRSTerm rhs = rule.getRight();

            boolean containsDefSym = false;
            // populate set of defined symbol positions (will be done for relative)
            // For each defined symbol occurrence, add an ADP with that symbol annotated
            for (final Pair<Position, TRSTerm> posAndSubterm : rhs.getPositionsWithSubTerms()) {
                if (posAndSubterm.y.isVariable()) {continue;}  // Skip if subterm is a variable

                final TRSFunctionApplication subterm = (TRSFunctionApplication) posAndSubterm.y;
                final FunctionSymbol root = subterm.getRootSymbol();

                if (!defSymbols.contains(root)) {continue;}  // Skip if subterm isn't defined symbol
                
                //At this point, we reached a defined symbol in the right-hand side
                containsDefSym = true;
                
                final Position pos = posAndSubterm.x;
                final FunctionSymbol anno_root = QTRSProblem.getTupleSymbol(root, annotatorMap, signature);
                final TRSFunctionApplication anno_subterm = TRSTerm.createFunctionApplication(
                    anno_root,
                    subterm.getArguments()
                );
                final TRSTerm anno_rhs = rhs.replaceAt(pos, anno_subterm);
                final Rule adp = Rule.create(lhs, anno_rhs);
                res.x.add(adp);
            }

            // The unannotated rule should be in as well if there are no defined symbols in the right-hand side
            if(!containsDefSym) {
                res.x.add(rule);
            }
        }

        for (Rule rule : S) {  // Relative Rules
            
            // A bit more complicated here, because we want to annotate up to two symbols per ADP.
            // First we build up a set of annotatable term positions, then we operate on all pairs of these.
            final TRSFunctionApplication lhs = rule.getLeft();
            final TRSTerm rhs = rule.getRight();
            final Set<Position> posD = new LinkedHashSet<Position>();

            Set<Rule> singleAnnoRules = new HashSet<>();
            
            // populate set of defined symbol positions.
            // but also do the same thing as in absolute (ADPs with one anno each).
            for (final Pair<Position, TRSTerm> posAndSubterm : rhs.getPositionsWithSubTerms()) {
                if (posAndSubterm.y.isVariable()) {continue;}  // Skip if subterm is a variable

                final TRSFunctionApplication subterm = (TRSFunctionApplication) posAndSubterm.y;
                final FunctionSymbol root = subterm.getRootSymbol();

                if (!defSymbols.contains(root)) {continue;}  // Skip if subterm isn't defined symbol

                final Position pos = posAndSubterm.x;
                final FunctionSymbol anno_root = QTRSProblem.getTupleSymbol(root, annotatorMap, signature);
                final TRSFunctionApplication anno_subterm = TRSTerm.createFunctionApplication(
                    anno_root,
                    subterm.getArguments()
                );
                final TRSTerm anno_rhs = rhs.replaceAt(pos, anno_subterm);
                
                final Rule adp = Rule.create(lhs, anno_rhs);
                singleAnnoRules.add(adp);

                posD.add(posAndSubterm.x);
            }

            switch(posD.size()) {
                case 0:
                    res.y.add(rule);
                    
                    break;
                case 1:
                    res.y.addAll(singleAnnoRules);
                    
                    break;
                default: //more than 2 def symbols 
                    // Go through position pairs and annotate as needed
                    for (Position pos1: posD) {
                        for (Position pos2: posD) {
                            // Skip reflexive and symmetric pairs
                            // (should work if hash is implemented properly)
                            // I don't think there's any kind of "cartesian product" code around
                            if (pos1.hashCode() >= pos2.hashCode()) {continue;}

                            final TRSFunctionApplication subterm1 = (TRSFunctionApplication) rhs.getSubterm(pos1);
                            final FunctionSymbol root1 = subterm1.getRootSymbol();
                            final TRSFunctionApplication anno_subterm1 = TRSTerm.createFunctionApplication(
                                QTRSProblem.getTupleSymbol(root1, annotatorMap, signature),
                                subterm1.getArguments()
                            );
                            TRSTerm anno_rhs = rhs.replaceAt(pos1, anno_subterm1);

                            // now do pos2
                            final TRSFunctionApplication subterm2 = (TRSFunctionApplication) anno_rhs.getSubterm(pos2);
                            final FunctionSymbol root2 = subterm2.getRootSymbol();
                            final TRSFunctionApplication anno_subterm2 = TRSTerm.createFunctionApplication(
                                QTRSProblem.getTupleSymbol(root2, annotatorMap, signature),
                                subterm2.getArguments()
                            );
                            anno_rhs = anno_rhs.replaceAt(pos2, anno_subterm2);
                            final Rule adp = Rule.create(lhs, anno_rhs);
                            res.y.add(adp);
                        }
                    }
            }

        }
        return new Pair<Pair<Set<Rule>, Set<Rule>>, Map<FunctionSymbol, FunctionSymbol>>(res, annotatorMap);
    }

    private void calculateDefSymbolsAndRuleMapOfR() {
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
        this.ruleMapOfR = ImmutableCreator.create(immutableMap);
        this.defSymbolsOfR = ImmutableCreator.create(immutableMap.keySet());
    }

    private void calculateDefSymbolsAndRuleMapOfS() {
        final Map<FunctionSymbol, Set<Rule>> ruleMap = new LinkedHashMap<FunctionSymbol, Set<Rule>>();
        for (final Rule rule : this.S) {
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
        this.ruleMapOfS = ImmutableCreator.create(immutableMap);
        this.defSymbolsOfS = ImmutableCreator.create(immutableMap.keySet());
    }

    /**
     * get R as a mapping from defined symbols to corresponding rules
     */
    public ImmutableMap<FunctionSymbol, ImmutableSet<Rule>> getRuleMapOfR() {
        if (this.ruleMapOfR == null) {
            synchronized(this) {
                if (this.ruleMapOfR == null) {
                    this.calculateDefSymbolsAndRuleMapOfR();
                }
            }
        }
        return this.ruleMapOfR;
    }

    /**
     * get S as a mapping from defined symbols to corresponding rules
     */
    public ImmutableMap<FunctionSymbol, ImmutableSet<Rule>> getRuleMapOfS() {
        if (this.ruleMapOfS == null) {
            synchronized(this) {
                if (this.ruleMapOfS == null) {
                    this.calculateDefSymbolsAndRuleMapOfR();
                }
            }
        }
        return this.ruleMapOfS;
    }

    private void calculateReverseRuleMapOfR() {
        final Map<FunctionSymbol, Set<Rule>> reverseRuleMap = new LinkedHashMap<FunctionSymbol, Set<Rule>>();
        for (final Rule rule : this.R) {
            final TRSTerm rhs = rule.getRight();
            if(rhs.isVariable()) {
                continue;
            }
            else {
                final TRSFunctionApplication fa = (TRSFunctionApplication) rhs;
                final FunctionSymbol fs = fa.getRootSymbol();

                Set<Rule> fsRules = reverseRuleMap.get(fs);
                if (fsRules == null) {
                    fsRules = new LinkedHashSet<Rule>();
                    reverseRuleMap.put(fs, fsRules);
                }
                fsRules.add(rule);
            }
        }
        final Map<FunctionSymbol, ImmutableSet<Rule>> immutableMap = new LinkedHashMap<FunctionSymbol, ImmutableSet<Rule>>();
        for (final Map.Entry<FunctionSymbol, Set<Rule>> entry : reverseRuleMap.entrySet()) {
            immutableMap.put(entry.getKey(), ImmutableCreator.create(entry.getValue()));
        }
        this.reverseRuleMapOfR = ImmutableCreator.create(immutableMap);
    }

    private void calculateReverseRuleMapOfS() {
        final Map<FunctionSymbol, Set<Rule>> reverseRuleMap = new LinkedHashMap<FunctionSymbol, Set<Rule>>();
        for (final Rule rule : this.S) {
            final TRSTerm rhs = rule.getRight();
            if(rhs.isVariable()) {
                continue;
            }
            else {
                final TRSFunctionApplication fa = (TRSFunctionApplication) rhs;
                final FunctionSymbol fs = fa.getRootSymbol();

                Set<Rule> fsRules = reverseRuleMap.get(fs);
                if (fsRules == null) {
                    fsRules = new LinkedHashSet<Rule>();
                    reverseRuleMap.put(fs, fsRules);
                }
                fsRules.add(rule);
            }
        }
        final Map<FunctionSymbol, ImmutableSet<Rule>> immutableMap = new LinkedHashMap<FunctionSymbol, ImmutableSet<Rule>>();
        for (final Map.Entry<FunctionSymbol, Set<Rule>> entry : reverseRuleMap.entrySet()) {
            immutableMap.put(entry.getKey(), ImmutableCreator.create(entry.getValue()));
        }
        this.reverseRuleMapOfS = ImmutableCreator.create(immutableMap);
    }

    /**
     * get R^{-1} as a mapping from function symbols of rhs to corresponding rules
     */
    public ImmutableMap<FunctionSymbol, ImmutableSet<Rule>> getReverseRuleMapOfR() {
        if(this.reverseRuleMapOfR == null) {
            synchronized(this) {
                if(this.reverseRuleMapOfR == null) {
                    this.calculateReverseRuleMapOfR();
                }
            }
        }
        return this.reverseRuleMapOfR;
    }

    /**
     * get S^{-1} as a mapping from function symbols of rhs to corresponding rules
     */
    public ImmutableMap<FunctionSymbol, ImmutableSet<Rule>> getReverseRuleMapOfS() {
        if(this.reverseRuleMapOfS == null) {
            synchronized(this) {
                if(this.reverseRuleMapOfS == null) {
                    this.calculateReverseRuleMapOfS();
                }
            }
        }
        return this.reverseRuleMapOfS;
    }

    /**
     * get all rules of R where the rhs is a variable
     */
    public ImmutableSet<Rule> getRRulesWhereRhsIsVariable() {
        final Set<Rule> rhsVar = new LinkedHashSet<Rule>();
        if(this.lhsWhereRhsIsVariableOfR == null) {
            for(final Rule rule : this.R) {
                if(rule.getRight().isVariable()) {
                    rhsVar.add(rule);
                }
            }
            this.lhsWhereRhsIsVariableOfR = ImmutableCreator.create(rhsVar);
        }
        return this.lhsWhereRhsIsVariableOfR;
    }

    /**
     * get all rules of S where the rhs is a variable
     */
    public ImmutableSet<Rule> getSRulesWhereRhsIsVariable() {
        final Set<Rule> rhsVar = new LinkedHashSet<Rule>();
        if(this.lhsWhereRhsIsVariableOfS == null) {
            for(final Rule rule : this.S) {
                if(rule.getRight().isVariable()) {
                    rhsVar.add(rule);
                }
            }
            this.lhsWhereRhsIsVariableOfS = ImmutableCreator.create(rhsVar);
        }
        return this.lhsWhereRhsIsVariableOfS;
    }


    public ImmutableSet<FunctionSymbol> getDefinedSymbolsOfR() {
        if (this.defSymbolsOfR == null) {
            synchronized(this) {
                if (this.defSymbolsOfR == null) {
                    this.calculateDefSymbolsAndRuleMapOfR();
                }
            }
        }
        return this.defSymbolsOfR;
    }

    public ImmutableSet<FunctionSymbol> getDefinedSymbolsOfS() {
        if (this.defSymbolsOfS == null) {
            synchronized(this) {
                if (this.defSymbolsOfS == null) {
                    this.calculateDefSymbolsAndRuleMapOfS();
                }
            }
        }
        return this.defSymbolsOfS;
    }

    public ImmutableSet<FunctionSymbol> getSignature() {
        if (this.signature == null) {
            this.computeRSignatures();
            this.computeSSignatures();
            final Set<FunctionSymbol> signature = new LinkedHashSet<FunctionSymbol>(this.Rsignature);
            signature.addAll(this.Ssignature);
            this.signature = ImmutableCreator.create(signature);
        }
        return this.signature;
    }

    public ImmutableSet<FunctionSymbol> getRSignature() {
        if (this.Rsignature == null) {
            this.computeRSignatures();
        }
        return this.Rsignature;
    }

    public ImmutableSet<FunctionSymbol> getSSignature() {
        if (this.Ssignature == null) {
            this.computeSSignatures();
        }
        return this.Ssignature;
    }

    private synchronized void computeRSignatures() {
        if (this.Rsignature == null) {
            final Set<FunctionSymbol> signature = CollectionUtils.getFunctionSymbols(this.R);
            this.Rsignature = ImmutableCreator.create(signature);
        }
    }

    private synchronized void computeSSignatures() {
        if (this.Ssignature == null) {
            final Set<FunctionSymbol> ssignature = CollectionUtils.getFunctionSymbols(this.S);
            this.Ssignature = ImmutableCreator.create(ssignature);
        }
    }

    /**
     * returns the set of terms in R and S,
     * the set may be modified
     */
    @Override
    public Set<TRSTerm> getTerms() {
        // terms of R
        final Set<TRSTerm> terms = CollectionUtils.getTerms(this.R);
        // plus terms of S
        terms.addAll(CollectionUtils.getTerms(this.S));
        return terms;
    }

    public RelTRSProblem createSubProblem(final ImmutableSet<Rule> rRules, final ImmutableSet<Rule> sRules) {
        if (Globals.useAssertions){
            assert(this.R.containsAll(rRules));
            assert(this.S.containsAll(sRules));
            assert(RelTRSProblem.checkRIntersectSisEmpty(rRules, sRules));
        }
        if (this.R.size() == rRules.size()) {
            if(this.S.size() == sRules.size()){
                if (Globals.DEBUG_ULRICHSG) {
                    System.out.println("Warning: createSubProblem in RelTRS produces identity");
                }
                return this;
            }
        }
        return new RelTRSProblem(rRules, sRules);
    }

    public boolean isSRS() {

        final Set<FunctionSymbol> fsyms = new LinkedHashSet<FunctionSymbol>();
        for (final Rule rule : this.R) {
            fsyms.addAll(rule.getLeft().getFunctionSymbols());
            fsyms.addAll(rule.getRight().getFunctionSymbols());
        }
        for (final Rule rule : this.S) {
            fsyms.addAll(rule.getLeft().getFunctionSymbols());
            fsyms.addAll(rule.getRight().getFunctionSymbols());
        }
        for (final FunctionSymbol f : fsyms) {
            if (f.getArity() > 1) {
                return false;
            }
        }
        return true;
    }

    public String getName() {
        return "Relative TRS";
    }

    /* (non-Javadoc)
     * @see aprove.prooftree.Obligations.BasicObligation#offersCertifiableTechniques()
     */
    @Override
    public boolean offersCertifiableTechniques() {
        return true;
    }

    @Override
    public String export(final Export_Util o) {
        final StringBuilder s = new StringBuilder();
        s.append(o.export("Relative term rewrite system:"));
        s.append(o.cond_linebreak());
        if (this.R.isEmpty()) {
            s.append("R is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("The relative TRS consists of the following R rules:"));
            s.append(o.cond_linebreak());
            s.append(o.set(this.R, Export_Util.RULES));
            s.append(o.cond_linebreak());
        }

        if (this.S.isEmpty()) {
            s.append("S is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("The relative TRS consists of the following S rules:"));
            s.append(o.cond_linebreak());
            s.append(o.set(this.S, Export_Util.RULES));
            s.append(o.cond_linebreak());
        }

        return s.toString();
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        final Element oblTag = XMLTag.RELTRS_OBL.createElement(doc);
        final Element problemTag = XMLTag.RELTRS.createElement(doc);
        final Element rTag = XMLTag.TRS.createElement(doc);
        CollectionUtils.addChildren(this.R, rTag, doc, xmlMetaData);
        problemTag.appendChild(rTag);
        final Element sTag = XMLTag.TRS.createElement(doc);
        CollectionUtils.addChildren(this.S, sTag, doc, xmlMetaData);
        problemTag.appendChild(sTag);
        final Element sigTag = XMLTag.SIGNATURE.createElement(doc);
        CollectionUtils.addChildren(this.getSignature(), sigTag, doc, xmlMetaData);
        problemTag.appendChild(sigTag);
        oblTag.appendChild(problemTag);
        return oblTag;
    }

    @Override
    public Element getCPFInput(final Document doc, final XMLMetaData xmlMetaData, final TruthValue tv) {
        return CPFTag.TRS_INPUT.create(doc,
                CPFTag.trs(doc, xmlMetaData, this.getR()),
                CPFTag.RELATIVE_RULES.create(doc,
                        CPFTag.rules(doc, xmlMetaData, this.getS())));
    }

    @Override
    public Element getCPFAssumption(
        final Document doc,
        final XMLMetaData xmlMetaData,
        final CPFModus modus,
        final TruthValue tv)
    {
        if (modus.isPositive()) {
            return CPFTag.RELATIVE_TERMINATION_PROOF.create(
                doc,
                CPFTag.RELATIVE_TERMINATION_ASSUMPTION.create(doc, this.getCPFInput(doc, xmlMetaData, tv)));
        } else {
            return CPFTag.RELATIVE_NONTERMINATION_PROOF.create(
                doc,
                CPFTag.NONTERMINATION_ASSUMPTION.create(doc, this.getCPFInput(doc, xmlMetaData, tv)));
        }
    }


    @Override
    public String toExternString() {
        final TRSGenerator trsGen =  new TRSGenerator();
        trsGen.writeRules(this.R);
        trsGen.writeRelativeRules(this.S);
        return trsGen.getTRSString(false, null);
    }

    @Override
    public String externName() {
        return "trs";
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
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new DefaultProofPurposeDescriptor(this, "Termination");
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getStrategyName() {
        if (this.isSRS()) {
            return "rsrs";
        } else {
            return "rtrs";
        }
    }
    
    /**
     * very simple fresh name generator
     */
    private static final class FunctionSymbolGenerator {

        private final Set<FunctionSymbol> fs;

        public FunctionSymbolGenerator(final int size) {
            this.fs = new HashSet<FunctionSymbol>(size);
        }

        public FunctionSymbol getFresh(final String name, final int arity) {
            int j = 0;
            String currentName = name;
            FunctionSymbol f;
            while (true) {
                f = FunctionSymbol.create(currentName, arity);
                if (this.fs.add(f)) {
                    return f;
                } else {
                    currentName = name + j;
                    j++;
                }
            }
        }

    }
}
