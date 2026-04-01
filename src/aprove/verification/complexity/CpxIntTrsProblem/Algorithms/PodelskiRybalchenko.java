package aprove.verification.complexity.CpxIntTrsProblem.Algorithms;

import java.util.*;
import java.util.Map.Entry;

import aprove.verification.complexity.CpxIntTrsProblem.Structures.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.SMTLIBRatComparison.*;
import aprove.verification.oldframework.Utility.*;

public class PodelskiRybalchenko {

    // assumption: impli is linear
    public static Formula<SMTLIBTheoryAtom> solve(
        RatPolImplication impli,
        FreshNameGenerator fng,
        FormulaFactory<SMTLIBTheoryAtom> factory)
    {
        List<Formula<SMTLIBTheoryAtom>> list = new ArrayList<>();
        for (RationalPolynomial geZero : impli.consequences) {
            list.add(PodelskiRybalchenko.buildFormula(geZero, impli, fng, factory));
        }
        return factory.buildAnd(list);
    }

    private static Formula<SMTLIBTheoryAtom> buildFormula(
        RationalPolynomial geZero,
        RatPolImplication impli,
        FreshNameGenerator fng,
        FormulaFactory<SMTLIBTheoryAtom> factory)
    {
        // TODO simplify by computing t_1 lam_1 + ... t_n lam_n + lam_{n+1} - p = 0 directly
        List<Formula<SMTLIBTheoryAtom>> list = new ArrayList<>();

        Map<IndefinitePart, RationalPolynomial> sum = new LinkedHashMap<>();
        Set<String> lams = new LinkedHashSet<>();
        Set<String> ex = new LinkedHashSet<>();
        ex.addAll(impli.existentialVars);

        Set<RationalPolynomial> s = new LinkedHashSet<>();
        s.addAll(impli.premises);
        s.add(RationalPolynomial.ONE); // 1 >= 0

        for (RationalPolynomial e : s) {
            String lam = fng.getFreshName("l", false);
            lams.add(lam);
            ex.add(lam);
            RationalPolynomial le = e.multiply(lam);
            for (Entry<IndefinitePart, RationalPolynomial> indefPol : le.split(ex).entrySet()) {
                IndefinitePart key = indefPol.getKey();
                RationalPolynomial curr = sum.get(key);
                if (curr == null) {
                    curr = RationalPolynomial.ZERO;
                }
                curr = curr.add(indefPol.getValue());
                sum.put(key, curr);
            }
        }
        for (Entry<IndefinitePart, RationalPolynomial> indefPol : geZero.negate().split(ex).entrySet()) {
            IndefinitePart key = indefPol.getKey();
            RationalPolynomial curr = sum.get(key);
            if (curr == null) {
                curr = RationalPolynomial.ZERO;
            }
            curr = curr.add(indefPol.getValue());
            sum.put(key, curr);
        }
        for (Entry<IndefinitePart, RationalPolynomial> e : sum.entrySet()) {
            IndefinitePart key = e.getKey();
            SMTLIBRatValue val = e.getValue().toSMTLIBRatValue();
            SMTLIBRatCMP v;
            if (key.isEmpty()) {
                v = SMTLIBRatLE.create(val, SMTLIBRatConstant.ZERO);
            } else {
                v = SMTLIBRatEquals.create(val, SMTLIBRatConstant.ZERO);
            }
            list.add(factory.buildTheoryAtom(v));
        }

        for (String l : lams) {
            list.add(factory.buildTheoryAtom(SMTLIBRatGE.create(SMTLIBRatVariable.create(l), SMTLIBRatConstant.ZERO)));
        }
        return factory.buildAnd(list);
    }

}
