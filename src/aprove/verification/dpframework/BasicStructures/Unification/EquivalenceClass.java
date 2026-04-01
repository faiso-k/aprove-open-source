package aprove.verification.dpframework.BasicStructures.Unification;

import java.util.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
/**
 * @author Matthias Sondermann
 * @version $Id$
 *
 * Equivalence class as a helper object for the rational unification algorithm
 */
public class EquivalenceClass {
    /**
     * represents the status of the class
     */
    public enum ClassStatus {
        UNKNOWN,
        INFINITE,
        FINITE,
        VARIABLE_CONFLICT,
        SYMBOL_CLASH;
    }
    /**
     * the representativ of the class which is a function node if there exists a function node in the class
     * (this property is given by the rational unification algorithm)
     */
    private RationalUnificationNode representative;
    /**
     * all members including the representative
     */
    private Set<RationalUnificationNode> members;
    /**
     * function symbol if the representative is a function node
     */
    private FunctionSymbol symbol;
    private ClassStatus status;

    public EquivalenceClass(RationalUnificationNode representative) {
        if(Globals.useAssertions) {
            assert(representative != null);
        }
        this.representative = representative;
        this.representative.addToEquivalenceClass(this);
        if(this.representative.isFunctionNode()) {
            this.symbol = ((TRSFunctionApplication) this.representative.getTerm()).getRootSymbol();
        }
        else {
            this.symbol = null;
        }
        this.members = new LinkedHashSet<RationalUnificationNode>();
        this.members.add(representative);
        this.status = ClassStatus.UNKNOWN;
    }

    public RationalUnificationNode getRepresentative() {
        return this.representative;
    }

    public Set<RationalUnificationNode> getMembers() {
        return this.members;
    }

    public FunctionSymbol getSymbol() {
        return this.symbol;
    }

    /**
     * Adds a new node to the class and checks for a symbol clash.
     * In that case the status is changed to SYMBOL_CLASH
     *
     * @return true iff <code>node</code> is a variable node and we
     *         know that the status is infinite
     */
    public boolean add(RationalUnificationNode node) {
        boolean newInfin = false;
        if(node.isFunctionNode()) {
            FunctionSymbol f = ((TRSFunctionApplication) node.getTerm()).getRootSymbol();
            if(! f.equals(this.symbol)) {
                this.status = ClassStatus.SYMBOL_CLASH;
            }
        }
        else {
            // node represents a variable
            if(this.status == ClassStatus.INFINITE) {
                newInfin = true;
            }
        }
        node.addToEquivalenceClass(this);
        this.members.add(node);
        return newInfin;
    }

    public ClassStatus getClassStatus(Set<TRSVariable> finiteVariables) {
        if(Globals.useAssertions) {
            assert(finiteVariables != null);
        }
        if(this.status == ClassStatus.SYMBOL_CLASH) {
            return ClassStatus.SYMBOL_CLASH;
        }
        Set<TRSVariable> infVars = new LinkedHashSet<TRSVariable>();
        Set<TRSVariable> variables = this.getVariablesOfEquivalenceClass();
        for(TRSFunctionApplication func : this.getFunctionApplicationsOfEquivalenceClass()) {
            Set<TRSVariable> funcVars = func.getVariables();
            for(TRSVariable var : variables) {
                if(funcVars.contains(var)) {
                    infVars.add(var);
                }
            }
        }
        if(! infVars.isEmpty()) {
            for(TRSVariable v : finiteVariables) {
                if(variables.contains(v)) {
                    return ClassStatus.VARIABLE_CONFLICT;
                }
            }
            return ClassStatus.INFINITE;
        }
        return ClassStatus.FINITE;
    }

    public boolean isVariableClass() {
        return this.symbol == null;
    }

    public boolean isFunctionClass() {
        return this.symbol != null;
    }

    public Set<RationalUnificationNode> getFunctionNodesOfEquivalenceClass() {
        Set<RationalUnificationNode> returnSet = new LinkedHashSet<RationalUnificationNode>();
        for(RationalUnificationNode node : this.members) {
            if(! node.getTerm().isVariable()) {
                returnSet.add(node);
            }
        }
        return returnSet;
    }

    public Set<RationalUnificationNode> getVariableNodesOfEquivalenceClass() {
        Set<RationalUnificationNode> returnSet = new LinkedHashSet<RationalUnificationNode>();
        for(RationalUnificationNode node : this.members) {
            if(node.getTerm().isVariable()) {
                returnSet.add(node);
            }
        }
        return returnSet;
    }

    public Set<TRSVariable> getVariablesOfEquivalenceClass() {
        Set<TRSVariable> returnSet = new LinkedHashSet<TRSVariable>();
        for(RationalUnificationNode node : this.members) {
            TRSTerm term = node.getTerm();
            if(term.isVariable()) {
                returnSet.add((TRSVariable) term);
            }
        }
        return returnSet;
    }

    public Set<TRSFunctionApplication> getFunctionApplicationsOfEquivalenceClass() {
        Set<TRSFunctionApplication> returnSet = new LinkedHashSet<TRSFunctionApplication>();
        for(RationalUnificationNode node : this.members) {
            TRSTerm term = node.getTerm();
            if(! term.isVariable()) {
                returnSet.add((TRSFunctionApplication) term);
            }
        }
        return returnSet;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        Iterator<RationalUnificationNode> it = this.members.iterator();
        if(it.hasNext()) {
            sb.append(it.next().getTerm());
        }
        while(it.hasNext()) {
            sb.append(", " + it.next().getTerm());
        }
        return sb.toString();
    }
}
