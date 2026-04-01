package aprove.verification.dpframework.CSDPProblem;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * Estimated CapMu function, should do exactly what Ren^\mu(Cap^\mu(t)) does for
 * the case NF^\mu(Q) = NV^\mu(R) or NF^\mu(Q) = {}. (Ren^\mu and Cap^\mu are
 * defined in "Termination of Innermost Context-Sensitive Rewriting Using
 * Dependency Pairs", B. Alarcon and S. Lucas, LNCS 4720:73-87, Springer-Verlag,
 * Berlin, 2007)
 *
 * @author fab
 * @version $Id$
 */
public class SimpleCapMu
        extends CapMuEstimation {

    public SimpleCapMu() {
    }

    @Override
    protected TRSTerm capMu(ReplacementMap mu, QTermSet q, GeneralizedTRS r,
            Set<TRSTerm> sTerms, TRSTerm term, boolean innermost,
            FreshNameGenerator gen) {
        if (term.isVariable()) {
            return gen.getNextFreshVariable();
        } else {
            TRSFunctionApplication t = (TRSFunctionApplication) term;
            FunctionSymbol f = t.getRootSymbol();

            if (r.getSymbolToRule().containsKey(f) || !r.getVarRules().isEmpty()) {
                /* f is a defined symbol or we have vars as lhs in a generalized TRS */
                return gen.getNextFreshVariable();
            }

            /* f is no defined symbol. construct new term recursively */
            int n = f.getArity();
            Set<Integer> map = mu.getMap().get(f);
            ArrayList<TRSTerm> args = new ArrayList<TRSTerm>(n);

            argument: for (int i = 0; i < n; ++i) {
                TRSTerm t_i = t.getArgument(i);
                if (map.contains(i)) {
                    // replacing position

                    // if we are in innermost case and s contains t as active
                    // subterm, copy
                    if (innermost) {
                        for (TRSTerm s : sTerms) {
                            if (mu.getReplacingSubterms(s).contains(t)) {
                                args.add(t_i);
                                continue argument;
                            }
                        }
                    }

                    // otherwise apply recursively
                    args.add(this.capMu(mu, q, r, sTerms, t_i, innermost, gen));

                } else {
                    // non-replacing position... copy
                    args.add(t_i);
                }
            }

            /*
             * if nothing changed, return old term for better performance/memory
             * usage
             */
            if (args.equals(t.getArguments())) {
                return t;
            }

            return TRSTerm.createFunctionApplication(f, ImmutableCreator
                    .create(args));
        }
    }
}