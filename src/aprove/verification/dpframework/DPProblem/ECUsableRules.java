/*
 * Created on Oct 30, 2006
 */
package aprove.verification.dpframework.DPProblem;


import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Unification.Equational.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * @author stein
 * @version $Id$
 *
 * Implementation of improved usable rules and equations of EDP Framework
 * for case that equations of the ETRS are only C-equations.
 */

public class ECUsableRules {

    protected static Logger logger = Logger.getLogger("aprove.verification.dpframework.DPProblem.ECUsableRules");


    private final ETRSProblem etrs;

    private ImmutableSet<Rule> P; //current P
    private ImmutableSet<Equation> eSharp; //current eSharp
    private ImmutableSet<Rule> usableR; //current UsableRules
    private ImmutableSet<Equation> usableE; //current UsableE

    private GeneralACnC unify; //E Unificator
    private Map<FunctionSymbol, Set<TRSFunctionApplication>> lhsRAsMap; // lhs of R in standard representation
                                                                    // this is essential for tcap!
    private Set<TRSTerm> calculated; //Set of terms where U(t) has already been calculated
                                   // to assert termination of usable rules calculation


    public ECUsableRules(ETRSProblem etrs) {
        if(Globals.useAssertions) {
            assert(etrs.checkC());
        }
        this.etrs = etrs;
        this.P = null;
        this.eSharp = null;
        this.usableR = null;
        this.usableE = null;
        this.calculated = null;

        this.unify = new GeneralACnC(new HashSet<FunctionSymbol>(), etrs.getCSymbols());
        this.lhsRAsMap = GeneralizedRule.computeLhsOfRulesAsMapInStandardRepresentation(etrs.getRuleMap());
    }

    /**
     * computes the usable rules for a given set of DPs, a set of Equations eSharp
     * and the underlying ETRS (which was passed in the constructor)
     */
    public ImmutableSet<Rule> getUsableRules(Collection<Rule> dps, Collection<Equation> eSharp) {
        //only calculate if necessary
        if( this.P == null || !this.P.equals(dps) || !this.eSharp.equals(eSharp)) {
            this.recalculateUsableRulesAndEquations(dps, eSharp);
        }
        return this.usableR;
    }

    /**
     * computes the usable equations for a given set of DPs, a set of Equations eSharp
     * and the underlying ETRS (which was passed in the constructor)
     */
    public ImmutableSet<Equation> getUsableEquations(Collection<Rule> dps, Collection<Equation> eSharp) {
        //only calculate if necessary
        if( this.P == null || !this.P.equals(dps) || !this.eSharp.equals(eSharp)) {
            this.recalculateUsableRulesAndEquations(dps, eSharp);
        }
        return this.usableE;
    }

    /**
     * Calculates the current improved usable rules and equations for the given DPs, eSharp and the underlying ETRS and
     * sets the current P and eSharp.
     */
    private void recalculateUsableRulesAndEquations(Collection<Rule> dps, Collection<Equation> eSharp) {

        this.calculated = new HashSet<TRSTerm>();
        HashSet<Object> U = new HashSet<Object>();
        HashSet<Object> N = new HashSet<Object>();
        N.addAll(this.etrs.getR());
        N.addAll(this.etrs.getE());

        Set<Rule> P = new HashSet<Rule>();
        for(Rule r:dps) {
            Set<Object> recursivelyRemoved = this.calcUsable(r.getRight(),N);
            N.removeAll(recursivelyRemoved);
            U.addAll(recursivelyRemoved);
            P.add(r);
        }
        Set<Equation> eS = new HashSet<Equation>();
        for(Equation es:eSharp) {
            Set<Object> recursivelyRemoved = this.calcUsable(es.getRight(),N);
            N.removeAll(recursivelyRemoved);
            U.addAll(recursivelyRemoved);
            recursivelyRemoved = this.calcUsable(es.getLeft(),N);
            N.removeAll(recursivelyRemoved);
            U.addAll(recursivelyRemoved);
            eS.add(es);
        }

        //get usableE and usableR out of U
        HashSet<Rule> uR = new HashSet<Rule>();
        HashSet<Equation> uE = new HashSet<Equation>();
        for(Object o:U) {
            if(o instanceof Rule) {
                uR.add((Rule)o);
            }
            else if(o instanceof Equation) {
                uE.add((Equation)o);
            }
        }

        this.P = ImmutableCreator.create(P);
        this.eSharp = ImmutableCreator.create(eS);
        this.usableR = ImmutableCreator.create(uR);
        this.usableE = ImmutableCreator.create(uE);
        ECUsableRules.logger.log(Level.FINE,"Calculated Improved Usable Rules/Equations:\n"+
                this.usableR.toString()+"\n"+this.usableE.toString()+"\n");
    }

    /**
     * Returns U(t) as usable rules and equations of N
     */
    private Set<Object> calcUsable(TRSTerm t, Set<Object> N) {

        Set<Object> removed = new HashSet<Object>();
        if(t.isVariable() || this.calculated.contains(t)) {
            return removed;
        }
        this.calculated.add(t);
        TRSTerm c_t = this.getct(t);

        //iterate over remaining non usable rules and eqns
        Set<Object> localN = new HashSet<Object>();
        localN.addAll(N);
        Iterator<Object> it = localN.iterator();
        Object obj;
        while(it.hasNext()) {
            obj = it.next();
            if(!removed.contains(obj)) {
                if(obj instanceof Rule){
                    Rule r = (Rule)obj;
                    //if c_t E-unifies with lhs of rule
                    //mark rule as usable and call recursively
                    if(this.unify.areTheoryUnifiable(c_t,r.getLeft().renumberVariables(TRSTerm.THIRD_STANDARD_PREFIX))) {
                        N.remove(obj);
                        removed.add(obj);
                        Set<Object> recursivelyRemoved = this.calcUsable(r.getRight(),N);
                        N.removeAll(recursivelyRemoved);
                        removed.addAll(recursivelyRemoved);
                    }
                }
                else if(obj instanceof Equation){
                    Equation e = (Equation)obj;
                    //if c_t E-unifies with lhs or rhs of eqn
                    //mark eqn as usable and call recursively
                    if( this.unify.areTheoryUnifiable(c_t,e.getLeft().renumberVariables(TRSTerm.THIRD_STANDARD_PREFIX)) ||
                    this.unify.areTheoryUnifiable(c_t,e.getRight().renumberVariables(TRSTerm.THIRD_STANDARD_PREFIX)) ){
                        N.remove(obj);
                        removed.add(obj);
                        Set<Object> recursivelyRemoved = this.calcUsable(e.getRight(),N);
                        N.removeAll(recursivelyRemoved);
                        removed.addAll(recursivelyRemoved);
                        recursivelyRemoved = this.calcUsable(e.getLeft(),N);
                        N.removeAll(recursivelyRemoved);
                        removed.addAll(recursivelyRemoved);
                    }
                }
            }
        }

        //recursive call for direct subterms of t
        if(!t.isVariable()){
            for(TRSTerm t_i:((TRSFunctionApplication)t).getArguments()){
                Set<Object> recursivelyRemoved = this.calcUsable(t_i,N);
                N.removeAll(recursivelyRemoved);
                removed.addAll(recursivelyRemoved);
            }
        }

        //recursive call for terms, E-equivalent to t
        Set<TRSTerm> CEquiv = this.etrs.getCEquivalent(t);
        CEquiv.remove(t);
        for(TRSTerm s: CEquiv) {
            Set<Object> recursivelyRemoved = this.calcUsable(s,N);
            N.removeAll(recursivelyRemoved);
            removed.addAll(recursivelyRemoved);
        }

        return removed;
    }

    private TRSTerm getct(TRSTerm t) {
        if(t.isVariable()) {
            return ((TRSVariable)t).tcapE(this.lhsRAsMap,new HashSet<FunctionSymbol>(), this.etrs.getCSymbols());
        }

        ArrayList<TRSTerm> args = new ArrayList<TRSTerm>();
        int n = 0;
        int nr = TRSTerm.STANDARD_NUMBER;
        Set<FunctionSymbol> A = new HashSet<>(0);
        for(TRSTerm t_i:((TRSFunctionApplication)t).getArguments()){
            ImmutablePair<TRSTerm, Integer> cti = t_i.tcapE(this.lhsRAsMap, A, this.etrs.getCSymbols(), nr);
            args.add(n,cti.x);
            nr = cti.y;
            n++;
        }
        return TRSTerm.createFunctionApplication(((TRSFunctionApplication)t).getRootSymbol(), ImmutableCreator.create(args));
    }
}

