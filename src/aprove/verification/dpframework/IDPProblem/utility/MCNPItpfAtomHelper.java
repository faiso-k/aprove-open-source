package aprove.verification.dpframework.IDPProblem.utility;

import java.util.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.Processors.IDPMCNPProcessor.*;
import aprove.verification.dpframework.IDPProblem.itpf.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Provides some auxiliary methods for Itpfs to help in getting from IDP
 * problems "as close as possible" to Monotonicity Constraints,
 * which we can then export for further processing.
 *
 * @author Carsten Fuhs
 */
public class MCNPItpfAtomHelper {

    private final IDPPredefinedMap predefinedMap;

    private MCNPItpfAtomHelper(IDPPredefinedMap predefinedMap) {
        this.predefinedMap = predefinedMap;
    }

    /**
     * @param predefinedMap
     * @return an MCNPItpfAtomHelper for the provided IDPPredefinedMap
     */
    public static MCNPItpfAtomHelper create(IDPPredefinedMap predefinedMap) {
        return new MCNPItpfAtomHelper(predefinedMap);
    }

    /**
     * @param itp
     * @return whether itp stands for an expression "s != t"
     */
    public boolean isNEQ(ItpfItp itp) {
        if (itp.getL().isVariable() || itp.getR().isVariable()) {
            return false;
        }
        if (itp.getRelation().isRewriteRel()) {
            return false;
        }

        FunctionSymbol fLeft = ((TRSFunctionApplication) itp.getL()).getRootSymbol();
        FunctionSymbol fRight = ((TRSFunctionApplication) itp.getR()).getRootSymbol();
        if (this.predefinedMap.isBooleanFalse(fRight)) {
            if (this.predefinedMap.isEq(fLeft)) {
                return true;
            }
        }
        else if (this.predefinedMap.isBooleanFalse(fLeft)) {
            if (this.predefinedMap.isEq(fRight)) {
                return true;
            }

        }
        return false;
    }


    /**
     * @param itpfDNF - may only contain instances of ItpfItp, ItpfTrue,
     *  ItpfFalse; non-null
     * @return equivalent DNF of ItpfItp's, where the disjunction of 0 args
     *  is equivalent to FALSE and the disjunction of >= 1 empty conjunctions
     *  is TRUE
     */
    public List<List<ItpfItp>> removeConstantsFromItpfDNF(List<List<ItpfAtom>> itpfDNF) {
        List<List<ItpfItp>> newDNF = new ArrayList<List<ItpfItp>>();
        for (List<ItpfAtom> oldConjunctiveClause : itpfDNF) {
            List<ItpfItp> newConjunctiveClause = new ArrayList<ItpfItp>();
            boolean keepConjunctiveClause = true;
            for (ItpfAtom itpAtom : oldConjunctiveClause) {
                if (itpAtom.isItp()) {
                    ItpfItp itp = (ItpfItp) itpAtom;
                    newConjunctiveClause.add(itp);
                }
                else if (itpAtom.isFalse()) {
                    keepConjunctiveClause = false;
                    break; // this disjunct won't become true, ever
                }
                else if (itpAtom.isTrue()) {
                    continue; // just ignore it
                }
                else {
                    throw new MCNPException("Cannot export ItpAtom " + itpAtom + "!");
                }
            }
            if (keepConjunctiveClause) {
                newDNF.add(newConjunctiveClause);
            }
        }
        return newDNF;
    }


    /**
     * @param itpfDNF may contain atoms that amount to "p != q"
     * @return an equivalent DNF without "!=" where we exploit that
     *  "p != q" is equivalent to "p > q OR q > p" and propagate
     */
    public List<List<ItpfItp>> removeNEQ(List<List<ItpfItp>> itpfDNF) {
        List<List<ItpfItp>> newDNF = new ArrayList<List<ItpfItp>>();
        for (List<ItpfItp> oldConjunctiveClause : itpfDNF) {
            // * first separate NEQ atoms from the rest
            List<ItpfItp> neqs, nonNeqs;
            neqs = new ArrayList<ItpfItp>();
            nonNeqs = new ArrayList<ItpfItp>();
            for (ItpfItp itp : oldConjunctiveClause) {
                if (this.isNEQ(itp)) {
                    neqs.add(itp);
                }
                else {
                    nonNeqs.add(itp);
                }
            }
            // * now export all of the 2^n LT/GT combinations for neqs,
            //   each combination followed by nonNeqs
            this.neqNonNeqToNonNeq(neqs, nonNeqs, newDNF);
        }
        return newDNF;
    }

    /**
     *
     * @param neqs
     * @param nonNeqs
     * @param addHere - here the resulting conjunctive clauses will be added
     */
    private void neqNonNeqToNonNeq(List<ItpfItp> neqs, List<ItpfItp> nonNeqs,
            List<List<ItpfItp>> addHere) {
        int neqsSize = neqs.size();
        if (Globals.useAssertions) {
            assert neqsSize <= 30;
        }
        ItpfItp[] gts = new ItpfItp[neqsSize];
        ItpfItp[] lts = new ItpfItp[neqsSize];
        for (int i = 0; i < neqsSize; ++i) {
            ItpfItp neq = neqs.get(i);
            gts[i] = this.neqToStrict(neq, true);
            lts[i] = this.neqToStrict(neq, false);
        }
        int numberOfCombs = AProVEMath.power(2, neqsSize);
        int entrySize = neqsSize + nonNeqs.size();
        for (int n = numberOfCombs-1; n >= 0; --n) {
            List<ItpfItp> currentEntry = new ArrayList<ItpfItp>(entrySize);
            int mask = 1; // masks exactly one bit of n
            for (int i = neqsSize-1; i >= 0; --i) {
                if ((n & mask) != 0) {
                    currentEntry.add(gts[i]);
                }
                else {
                    currentEntry.add(lts[i]);
                }
                mask <<= 1; // mask the next bit
            }
            currentEntry.addAll(nonNeqs);
            addHere.add(currentEntry);
        }
    }

    private ItpfItp neqToStrict(ItpfItp neq, boolean gt) {
        // neq should have the shape "=(s, t) REL FALSE" or "FALSE REL =(s, t)"
        // for a non-rewrite relation REL (which is blissfully ignored, actually)
        if (Globals.useAssertions) {
            assert this.isNEQ(neq);
        }

        // we want to express "s > t" (or "t > s", respectively), which is
        // encoded in the Itpf setting via ">(s, t) ABSTRACT_GT TRUE"
        TRSFunctionApplication fAppLeft = (TRSFunctionApplication) neq.getL();
        TRSFunctionApplication fAppRight = (TRSFunctionApplication) neq.getR();
        FunctionSymbol fLeft = fAppLeft.getRootSymbol();
        TRSFunctionApplication comparisonArgHaver = this.predefinedMap.isEq(fLeft) ? fAppLeft : fAppRight;
        ArrayList<TRSTerm> newComparisonArgs = new ArrayList<TRSTerm>(2);
        if (gt) {
            newComparisonArgs.add(comparisonArgHaver.getArgument(0));
            newComparisonArgs.add(comparisonArgHaver.getArgument(1));
        }
        else {
            newComparisonArgs.add(comparisonArgHaver.getArgument(1));
            newComparisonArgs.add(comparisonArgHaver.getArgument(0));;
        }
        // use the pre-defined gt symbol
        FunctionSymbol greaterThan = this.predefinedMap.getSym(Func.Gt, DomainFactory.INTEGERS);
        TRSTerm newComp = TRSTerm.createFunctionApplication(greaterThan, newComparisonArgs);
        TRSTerm trueTerm = this.predefinedMap.getBooleanTrue().getTerm();

        ItpfItp result = ItpfItp.create(newComp, ItpRelation.ABSTRACT_GT, trueTerm, neq.getS());
        return result;
    }

    /**
     * @param var
     * @return itp encoding of "var >= 0" (i.e., ">=(var, 0) ABSTRACT_GE TRUE")
     */
    public ItpfItp varGeqZero(TRSVariable var) {
        FunctionSymbol greaterEquals = this.predefinedMap.getSym(Func.Ge, DomainFactory.INTEGERS);
        TRSTerm zero = this.predefinedMap.getIntTerm(BigIntImmutable.ZERO, DomainFactory.INTEGERS);
        ArrayList<TRSTerm> args = new ArrayList<TRSTerm>(2);
        args.add(var);
        args.add(zero);
        TRSTerm lhs = TRSTerm.createFunctionApplication(greaterEquals, args);
        TRSTerm rhs = this.predefinedMap.getBooleanTrue().getTerm();
        ImmutableSet<TRSTerm> S = ImmutableCreator.create(java.util.Collections.<TRSTerm>singleton(var));
        ItpfItp result = ItpfItp.create(lhs, ItpRelation.ABSTRACT_GE, rhs, S);
        return result;
    }

    public List<ItpfItp> getVarsGeqZero(List<TRSVariable> vars) {
        List<ItpfItp> res = new ArrayList<ItpfItp>(vars.size());
        this.collectVarsGeqZero(vars, res);
        return res;
    }

    /**
     * @param vars - non-null
     * @param itps - for all var in vars, an itp encoding of "var >= 0"
     *  (i.e., ">=(var, 0) ABSTRACT_GE TRUE") shall be collected here
     */
    public void collectVarsGeqZero(List<TRSVariable> vars, List<ItpfItp> itps) {
        for (TRSVariable var : vars) {
            itps.add(this.varGeqZero(var));
        }
    }

    /**
     * @param factors
     * @param dnf
     * @return "map ((++) factors) dnf" (Haskell allows for less boilerplate)
     */
    public <T> List<List<T>> conjoinToDNF(List<T> factors, List<List<T>> dnf) {
        int factorsSize = factors.size();
        List<List<T>> res = new ArrayList<List<T>>(dnf.size());
        for (List<T> oldConjunctiveClause : dnf) {
            List<T> newConjunctiveClause = new ArrayList<T>(factorsSize+oldConjunctiveClause.size());
            newConjunctiveClause.addAll(factors);
            newConjunctiveClause.addAll(oldConjunctiveClause);
            res.add(newConjunctiveClause);
        }
        return res;
    }
}
