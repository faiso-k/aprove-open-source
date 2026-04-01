package aprove.verification.oldframework.CostEquationSystem;

import java.text.ParseException;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Annotations.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Algebra.MinMaxExprs.*;
import aprove.verification.oldframework.Algebra.MinMaxExprs.MinMaxExprParser.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Bytecode.Processors.ToMethodSummary.MethodSummaryBuilder.*;

public class CESBackendForMethodSummaryProcessor extends CESBackendProcessor {

    @ParamsViaArgumentObject
    public CESBackendForMethodSummaryProcessor(Arguments args) {
        super(args);
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return obl instanceof CESForMethodSummary;
    }

    @Override
    protected Result onCoFloCoSucces(CostEquationSystem obl, ComplexityValue cv, String poly, List<String> args, List<String> proof) {
        CESForMethodSummary ces = (CESForMethodSummary) obl;
        Task task = ces.getTask();
        if (poly != null) {
            try {
                SimplePolynomial res = SimplePolynomial.ZERO;
                for (SimplePolynomial p : MinMaxExprParser.parse(poly).toPolySet().x) {
                    res = res.plus(p);
                }

                Map<String, String> polyReplaceMap = new LinkedHashMap<>();
                for (int i=0; i<args.size(); i++) {
                    polyReplaceMap.put(args.get(i), ces.getStartTermArgMap().get(i).getStringRepresentation());
                }

                task.finish(res.replace(polyReplaceMap));
            } catch (ParseException | InfiniteException e) {
                task.fail(e);
            }
        } else {
            task.fail(new Exception("Koat fail"));
        }

        return super.onCoFloCoSucces(ces, cv, poly, args, proof);
    }

    @Override
    protected Result onCoFloCoFail(CostEquationSystem ces, Exception e) {
        ((CESForMethodSummary)ces).getTask().fail(e);
        return super.onCoFloCoFail(ces, e);
    }





}
