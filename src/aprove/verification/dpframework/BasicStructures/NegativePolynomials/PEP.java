/*
 * Created on 15.03.2005
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package aprove.verification.dpframework.BasicStructures.NegativePolynomials;

import java.util.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class PEP {

    /**
     * a PEP is a partially evaluated polynomial (w.r.t. to some Interpretation)
     * it is build from constants, variables, max-operators, uninterpreted terms
     * and positive linear combinations of these basic PEPs
     * (constants are not represented as basic PEPs, but handled inside PEPs itself)
     * However, on root level (and only on root level) it is allowed to have arbitrary
     * linear combinations, i.e., here negative coefficients are allowed.
     * Note that constants may be negative on their own, here is no restriction on only
     * positive constants below the root!
     */
    private final LinkedHashMap<BasicPEP, Integer> pepMap; // the mapping from Basic Peps to coefficients
    private final int constant; // the constant part of this PEP

    private final Set<FunctionSymbol> missInterpretations; // the function symbols where we need further interpretation

    private final int hashCode; // cached hashCode

    private final boolean nonNegative; // cached value that pet >= 0 for all specializations

    // cached PEVLs
    private PEVL cacheLeft;
    private PEVL cacheRight;
    private Pair<PEVL, PEVL> pevlConstraintCache;

    private final boolean allowNegative; // flag indicating that we only use positive interpretation
    // this allows us to not use deMaximize as max-polys are not required

    private PEP(LinkedHashMap<BasicPEP, Integer> pepMap, int constant, boolean allowNegative) {
        this.constant = constant;
        this.pepMap = pepMap;
        this.allowNegative = allowNegative;

        boolean nonNeg = constant >= 0;

        this.missInterpretations = new LinkedHashSet<FunctionSymbol>();

        for (Map.Entry<BasicPEP, Integer> entry : pepMap.entrySet()) {
            BasicPEP bPEP = entry.getKey();
            this.missInterpretations.addAll(bPEP.getMissingInterpretations());
            if (entry.getValue().intValue() < 0) {
                nonNeg = false;
            }
        }
        this.nonNegative = nonNeg;
        this.hashCode = this.constant*4890223+this.pepMap.hashCode()*923701223;
        this.cacheLeft = null;
        this.cacheRight = null;
        this.pevlConstraintCache = null;
    }

    /**
     * creates a pet from a constant nr
     * @param nr
     * @return
     */
    static PEP create(int nr, boolean allowNegative) {
        return new PEP(new LinkedHashMap<BasicPEP, Integer>(), nr, allowNegative);
    }

    /**
     * creates the pet 1*bPET
     * @param bPET
     * @return
     */
    static PEP create(BasicPEP bPET, boolean allowNegative) {
        LinkedHashMap<BasicPEP, Integer> polyMap = new LinkedHashMap<BasicPEP, Integer>();
        polyMap.put(bPET, 1);
        return new PEP(polyMap, 0, allowNegative);
    }

    public static PEP create(Rule rule, boolean strict, boolean allowNegative) {
        PEP pep = PEP.create(rule.getLeft(), allowNegative);
        pep = pep.subtract(PEP.create(rule.getRight(), allowNegative));
        if (strict) {
            pep = pep.subtract(PEP.create(1, allowNegative));
        }
        return pep;
    }

    public static PEP create(Constraint<TRSTerm> c, boolean allowNegative) {
        OrderRelation type = c.getType();
        boolean strict;
        switch (type) {
        case GR:
            strict = true;
            break;
        case GE:
            strict = false;
            break;
        default:
            throw new RuntimeException("Cannot deal with contraint type: "+type);
        }

        PEP pep = PEP.create(c.getLeft(), allowNegative);
        pep = pep.subtract(PEP.create(c.getRight(), allowNegative));
        if (strict) {
            pep = pep.subtract(PEP.create(1, allowNegative));
        }
        return pep;
    }

    /**
     * creates the completely unspecialized PET for the given term t
     * @param t
     * @return
     */
    public static PEP create(TRSTerm t, boolean allowNegative) {
        BasicPEP bPEP;
        if (t instanceof TRSVariable) {
            TRSVariable v = (TRSVariable) t;
            bPEP = VariablePEP.create(v.getName());
        } else if (t instanceof TRSFunctionApplication) {
            TRSFunctionApplication ft = (TRSFunctionApplication) t;
            FunctionSymbol f = ft.getRootSymbol();
            List<? extends TRSTerm> args = ft.getArguments();
            PEP[] pArgs = new PEP[args.size()];
            int i = 0;
            for (TRSTerm arg : args) {
                pArgs[i] = PEP.create(arg, allowNegative);
                i++;
            }
            bPEP = UnEvaluatedPEP.create(f, pArgs, allowNegative);
        } else {
            throw new RuntimeException("Unknown Term type in PET-Creation");
        }
        return PEP.create(bPEP, allowNegative);
    }

    /**
     * returns a specialized PET by giving an interpretation for f
     * @param f
     * @param interpretation
     * @return
     */
    public PEP specialize(FunctionSymbol f, int[] interpretation) {
        if (this.getMissingInterpretations().contains(f)) {
            int newConstant = this.constant;
            LinkedHashMap<BasicPEP, Integer> newPepMap = new LinkedHashMap<BasicPEP, Integer>();
            for (Map.Entry<BasicPEP, Integer> entry : this.pepMap.entrySet()) {
                BasicPEP bPEP = entry.getKey();
                int value = entry.getValue().intValue();
                if (bPEP.getMissingInterpretations().contains(f)) {
                    PEP newPEP = bPEP.specialize(f, interpretation);
                    // add newPET into our values newPepMap, newConstant
                    newConstant = PEP.addPEPtoMap(newPepMap, newConstant, newPEP, value);
                } else {
                    PEP.addBasicPEP(newPepMap, bPEP, value);
                }
            }
            return new PEP(newPepMap, newConstant, this.allowNegative);
        } else {
            return this;
        }
    }

    /**
     * returns a specialized PET by giving an interpretation
     * @param interpretation
     * @return
     */
    public PEP specialize(Map<FunctionSymbol, int[]> interpretation) {
        PEP newPep = this;
        for (Map.Entry<FunctionSymbol, int[]> inter : interpretation.entrySet()) {
            newPep = newPep.specialize(inter.getKey(), inter.getValue());
        }
        return newPep;
    }

    /**
     * specializes a given constraint pet with f/specialization
     * @param pep
     * @param f
     * @param specialization
     * @return null, if pet is not changed.
     *  <null, newPet>, if pet is changed and the truth value of the newPet is unknown
     *  <True/False, null>, if pet is changed and the truth value of the newPet is True/False
     */
    public static Pair<Boolean, PEP> specialize(PEP pep, FunctionSymbol f, int[] specialization) {
        Set<FunctionSymbol> missing = pep.getMissingInterpretations();
        Pair<Boolean, PEP> result = null;
        if (missing.contains(f)) {
            result = new Pair<Boolean, PEP>(null, null);
            pep = pep.specialize(f, specialization);
            YNM status = pep.getStatus();
            if (status != YNM.MAYBE) {
                result.x = status.toBool();
            } else {
                result.y = pep;
            }
        }
        return result;
    }

    public PEVL createPEVL(boolean leftMode) {
        if ((leftMode && this.cacheLeft == null) || (!leftMode && this.cacheRight == null)) {
            int n = this.pepMap.size();
            PEVL[] args = new PEVL[n];
            int i = 0;
            for (Map.Entry<BasicPEP, Integer> entry : this.pepMap.entrySet()) {
                // sanity check
                if (entry.getValue() < 0) {
                    throw new RuntimeException("One is not allowed to create a PEVL from a negative PEP");
                }
                args[i] = entry.getKey().createPEVL(leftMode);
                i++;
            }
            PEVL pevl = PEVL.create(null, args, leftMode);
            if (leftMode) {
                this.cacheLeft = pevl;
            } else {
                this.cacheRight = pevl;
            }
            return pevl;
        } else {
            if (leftMode) {
                return this.cacheLeft;
            } else {
                return this.cacheRight;
            }
        }
    }


    public Pair<PEVL, PEVL> createPEVLConstraint() {
        if (this.pevlConstraintCache == null) {
            LinkedHashMap<BasicPEP, Integer> left = new LinkedHashMap<BasicPEP, Integer>();
            LinkedHashMap<BasicPEP, Integer> right = new LinkedHashMap<BasicPEP, Integer>();
            for (Map.Entry<BasicPEP, Integer> entry : this.pepMap.entrySet()) {
                int i = entry.getValue().intValue();
                if (i > 0) {
                    left.put(entry.getKey(), i);
                } else {
                    right.put(entry.getKey(), -i);
                }
            }
            PEVL leftPEVL = new PEP(left, 0, this.allowNegative).createPEVL(true); // one may replace allowNegative by false
            PEVL rightPEVL = new PEP(right, 0, this.allowNegative).createPEVL(false); // in this cases as variables are not affected from max
            this.pevlConstraintCache = new Pair<PEVL, PEVL>(leftPEVL, rightPEVL);
        }
        return new Pair<PEVL, PEVL>(this.pevlConstraintCache.x, this.pevlConstraintCache.y);
    }

    /**
     * adds factor*bPEP destructively into the the map
     */
    private static void addBasicPEP(LinkedHashMap<BasicPEP, Integer> map, BasicPEP bPEP, int factor) {
        Integer prev = map.get(bPEP);
        int newValue = prev == null ? 0 : prev.intValue();
        newValue += factor;
        if (newValue == 0) {
            map.remove(bPEP);
        } else {
            map.put(bPEP, newValue);
        }
    }

    /**
     * return this+(factor*other)
     * @param other
     * @param factor
     * @return
     */
    public PEP add(PEP other, int factor) {
        // copy pep-map as addPETtoMap is destrucive!
        LinkedHashMap<BasicPEP, Integer> newPepMap = new LinkedHashMap<BasicPEP, Integer>(this.pepMap);

        int newConstant = PEP.addPEPtoMap(newPepMap, this.constant, other, factor);

        return new PEP(newPepMap, newConstant, this.allowNegative);
    }

    /**
     * adds the factor*pet destructively into the map
     * and returns the constant of the new pet
     */
    private static int addPEPtoMap(LinkedHashMap<BasicPEP, Integer> map, int oldConstant, PEP pep, int factor) {
        // calculate new PolyMap
        for (Map.Entry<BasicPEP,Integer> entry : pep.pepMap.entrySet()) {
            BasicPEP bPEP = entry.getKey();
            Integer value = entry.getValue();
            PEP.addBasicPEP(map, bPEP, value.intValue() * factor);
        }

        // and new constant
        int newConstant = oldConstant + pep.constant * factor;

        return newConstant;
    }

    /**
     * computes this-other
     * @param other
     * @return
     */
    public PEP subtract(PEP other) {
        return this.add(other, -1);
    }

    /**
     * computes the set of those FunctionSymbols, whose Interpretation is missing to
     * fully evaluate this PEP
     * @return
     */
    public Set<FunctionSymbol> getMissingInterpretations() {
        return this.missInterpretations;
    }

    public boolean isCompletelySpecified() {
        return this.missInterpretations.isEmpty();
    }

    /**
     * approximates whether this PEP will be non-negative for all specializations
     * @return
     */
    public boolean isNonNegative() {
        return this.nonNegative;
    }

    /**
     * for a fully specified PET this method calculates whether it is
     * non-negative. Here, max-Values are approximated.
     */
    public boolean checkNonNegative() {
        if (!this.allowNegative) {
            return this.nonNegative;
        }
        if (this.nonNegative) {
            return true;
        }
        return this.deMaximize(null).isNonNegative();
    }

    /**
     * tries to determine (un)satisfiability of this pet as constraint
     */
    public YNM getStatus() {
        if (this.nonNegative) {
            return YNM.YES;
        }
        if (this.isCompletelySpecified()) {
            return YNM.fromBool(this.checkNonNegative());
        } else {
            return YNM.MAYBE;
        }
    }

    public PEP deMaximize(Boolean left) {
        if (Globals.useAssertions) {
            assert(this.allowNegative);
        }
        boolean topMode = left == null;
        if (topMode && !this.isCompletelySpecified()) {
            // sanity check
            throw new RuntimeException("Cannot deMaxime a not completely specified PET!");
        }
        int newConstant = this.constant;
        LinkedHashMap<BasicPEP, Integer> newPolyMap = new LinkedHashMap<BasicPEP, Integer>();
        for (Map.Entry<BasicPEP, Integer> entry : this.pepMap.entrySet()) {
            BasicPEP bPEP = entry.getKey();
            int value = entry.getValue().intValue();
            if (topMode) {
                left = value > 0 ? true : false;
            }
            PEP newPET = bPEP.deMaximize(left);
            // add newPET into our values newPolyMap, newConstant
            newConstant = PEP.addPEPtoMap(newPolyMap, newConstant, newPET, value);
        }
        return new PEP(newPolyMap, newConstant, true);
    }

    PEP deMaximizeTop(Boolean left) {
        if (Globals.useAssertions) {
            assert(this.allowNegative);
        }
        if (left) {
            if (this.constant < 0) {
                if (this.pepMap.isEmpty()) {
                    return PEP.create(0, true);
                }
            }
            return this;
        } else {
            if (this.constant < 0) {
                return new PEP(this.pepMap, 0, this.allowNegative);
            } else {
                return this;
            }
        }
    }

    @Override
    public boolean equals(Object other) {
        if (other instanceof PEP) {
            PEP pep = (PEP) other;
            if (pep.hashCode != this.hashCode || pep.constant != this.constant) {
                return false;
            }
            return pep.pepMap.equals(this.pepMap);
        } else {
            return false;
        }
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

    @Override
    public String toString() {
        if (this.pepMap.isEmpty()) {
            return ""+this.constant;
        }
        boolean first;
        String s;
        if (this.constant != 0) {
            first = false;
            s = ""+this.constant;
        } else {
            first = true;
            s = "";
        }
        for (Map.Entry<BasicPEP, Integer> entry : this.pepMap.entrySet()) {
            int value = entry.getValue().intValue();
            if (first) {
                first = false;
                s += value > 0 ? "" : "-";
            } else {
                s += value > 0 ? "+" : "-";
            }
            value = value > 0 ? value : (-value);
            s += (value > 1 ? (""+value) : "")+entry.getKey();
        }

        return s;
    }

}
