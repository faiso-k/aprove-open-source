/*
 * Created on Jul 3, 2006
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
 * Calculates the usable ESharp Euqations
 *
 * @author stein
 * @version $Id$
 */

public class ESharpUsableEquations {

    protected static Logger logger = Logger.getLogger("aprove.verification.dpframework.DPProblem.ESharpUsableEquations");


    private final ETRSProblem etrs;

    private ImmutableSet<Rule> P; //current P
    private ImmutableSet<Equation> eSharp; //current eSharp
    private ImmutableSet<Equation> usableESharp; //current Usable Equations of ESharp

    public ESharpUsableEquations(ETRSProblem etrs) {
        this.etrs = etrs;
        this.P = null;
        this.eSharp = null;
        this.usableESharp = null;
    }


    /**
     * computes the usable equations of eSharp for a given set of DPs, eSharp
     * and the underlying ETRS (which was passed in the constructor)
     */
    public ImmutableSet<Equation> getUsableEquations(Collection<Rule> dps, Collection<Equation> eSharp) {
        //only correct for ACandAandC Equations
        if(Globals.useAssertions) {
            assert(this.etrs.checkACandAandC());
        }

        //  only calculate if necessary
        if(this.usableESharp == null || this.P == null || this.eSharp == null || !this.P.equals(dps) || !this.eSharp.equals(eSharp)) {
            this.recalculateUsableEquations(dps, eSharp);
        }
        return this.usableESharp;
    }


    /**
     * Calculates the usable ESharp Equations for the underlying ETRS, P and eSharp.
     */
    private void recalculateUsableEquations(Collection<Rule> dps, Collection<Equation> eSharp) {
        this.P = ImmutableCreator.create(new HashSet<Rule>(dps));
        this.eSharp = ImmutableCreator.create(new HashSet<Equation>(eSharp));

        // use a map so that already "to delete" marked equations haven't to be checked anymore
        Map<Equation, Boolean> toDeleteMap = new HashMap<Equation,Boolean>();
        for(Equation eq:eSharp) {
            toDeleteMap.put(eq,false);
        }


        for(Equation eq:eSharp) {
            if(toDeleteMap.get(eq) == false) {
                if(eq.checkCEquation()) {
                    if(this.doesntUnify(dps,eq)) {
                        //remove C Equation
                        toDeleteMap.put(eq,true);
                        //search for corresponding Asharp equation or equation with F as root and remove it
                        FunctionSymbol F = ((TRSFunctionApplication)(eq.getLeft())).getRootSymbol();
                        for(Equation eqA:eSharp) {
                            if(!toDeleteMap.get(eqA) && ((TRSFunctionApplication)(eqA.getLeft())).getRootSymbol().equals(F)) {
                                toDeleteMap.put(eqA,true);
                            }
                        }
                    }
                }
                else if(!toDeleteMap.get(eq) && eq.checkSharpedAEquation()) {
                    if(this.doesntUnify(dps,eq)) {
                        //remove Asharp Equation
                        toDeleteMap.put(eq,true);
                    }
                }
            }
        }

        // delete marked Equations
        for(Equation eq:eSharp) {
            if(toDeleteMap.get(eq) == true) {
                toDeleteMap.remove(eq);
            }
        }

        this.usableESharp = ImmutableCreator.create(toDeleteMap.keySet());
    }

    /**
     * Returns true iff tcap_e of all rhs of dps or all lhs of dps don't unify with the lhs or rhs of the eq
     *  -> so eq is not usable in eSharp anymore.
     */
    private boolean doesntUnify(Collection<Rule> dps, Equation eq) {

        FunctionSymbol F = ((TRSFunctionApplication)(eq.getLeft())).getRootSymbol();
        //if the corresponding associative Equation is in E, e-unification is necessary
        Equation aEq = Equation.createAEquation(F);
        if(this.etrs.getE().contains(aEq)) {
            //so here is E-unification necessary:
            //check if tcap_e of all rhs \in dps or all lhs of dps don't E-unify eq, then eliminate eq from eSharp
            boolean redundant = true;
            //take AC-unification as E-unification, cause cannot handle A-unification
            Set<FunctionSymbol> ACs = new HashSet<FunctionSymbol>();
            ACs.add(F);
            for(Rule pair : dps) {
                TRSTerm t = pair.getRight();
                if (t.isVariable()) {
                    redundant = false;
                    break;
                } else {
                    FunctionSymbol f = ((TRSFunctionApplication) t).getRootSymbol();
                    if(f.equals(F) || this.etrs.getDefinedSymbolsOfR().contains(f)) {
                        TRSTerm tcapT = pair.getRight().tcapE(
                                GeneralizedRule.computeLhsOfRulesAsMapInStandardRepresentation(this.etrs.getRuleMap()), this.etrs.getACandASymbols(), this.etrs.getCSymbols());
                        if(tcapT.isVariable()) {
                            redundant = false;
                            break;
                        }
                        else{
                            TRSTerm left = ((TRSFunctionApplication)tcapT).renumberVariables(TRSTerm.SECOND_STANDARD_PREFIX);

                            if(new GeneralAC(ACs).areTheoryUnifiable(left,eq.getLeft().renumberVariables(TRSTerm.STANDARD_PREFIX)) ||
                                    new GeneralAC(ACs).areTheoryUnifiable(left,eq.getRight().renumberVariables(TRSTerm.STANDARD_PREFIX)) ) {
                                redundant = false;
                                break;
                            }
                        }
                    }
                }
            }
            if(!redundant) {
                redundant = true;
                for(Rule pair : dps) {
                    FunctionSymbol f = ((TRSFunctionApplication) pair.getLeft()).getRootSymbol();
                    if(f.equals(F)) {
                        TRSTerm left = pair.getLeft().renumberVariables(TRSTerm.SECOND_STANDARD_PREFIX);
                        if(new GeneralAC(ACs).areTheoryUnifiable(left, eq.getLeft().renumberVariables(TRSTerm.STANDARD_PREFIX)) ||
                                new GeneralAC(ACs).areTheoryUnifiable(left, eq.getRight().renumberVariables(TRSTerm.STANDARD_PREFIX))) {
                            redundant = false;
                            break;
                        }
                    }
                }
            }
            //check if eq is redundant remove it
            if(redundant){
                return true;
            }

        }
        else {
            //here syntactic unification is sufficient in the ACnAnC case
            //check if tcap_e of all rhs \in dps or all lhs of dps don't unify eq, then eliminate eq from eSharp
            boolean redundant = true;
            for(Rule pair : dps) {
                TRSTerm t = pair.getRight();
                if (t.isVariable()) {
                    redundant = false;
                    break;
                } else {
                    FunctionSymbol f = ((TRSFunctionApplication) t).getRootSymbol();
                    if(f.equals(F) || this.etrs.getDefinedSymbolsOfR().contains(f)) {
                        TRSTerm tcapT = pair.getRight().tcapE(
                                GeneralizedRule.computeLhsOfRulesAsMapInStandardRepresentation(this.etrs.getRuleMap()), this.etrs.getACandASymbols(), this.etrs.getCSymbols());
                        if(tcapT.isVariable()) {
                            redundant = false;
                            break;
                        }
                        else if(tcapT.unifiesVarDisjoint(eq.getLeft()) ||  tcapT.unifiesVarDisjoint(eq.getRight())) {
                            redundant = false;
                            break;
                        }
                    }
                }
            }
            if(!redundant) {
                redundant = true;
                for(Rule pair : dps) {
                    FunctionSymbol f = ((TRSFunctionApplication) pair.getLeft()).getRootSymbol();
                    if(f.equals(F)) {
                        if (pair.getLeft().unifiesVarDisjoint(eq.getLeft()) || pair.getLeft().unifiesVarDisjoint(eq.getRight())) {
                            redundant = false;
                            break;
                        }
                    }
                }
            }
            //check if eq is redundant remove it
            if(redundant){
                return true;
            }
        }
        return false;
    }


}

