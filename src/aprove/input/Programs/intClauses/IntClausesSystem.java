package aprove.input.Programs.intClauses;

import java.util.*;

import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import immutables.*;

/**
 * Representation of integer transition systems in clauses form, as used by HSF.
 *
 * @author Marc Brockschmidt
 */
public class IntClausesSystem extends DefaultBasicObligation {
    /** Start location of the system. */
    private final Integer startLoc;

    /** Variables used in the system. */
    private final ImmutableList<TRSVariable> variables;

    /** Set of transitions in the system. */
    private final ImmutableSet<IntTransitionClause> transitions;

    public IntClausesSystem(final Integer start, final ArrayList<TRSVariable> vars, final Set<IntTransitionClause> trans) {
        this.startLoc = start;
        this.variables = ImmutableCreator.create(vars);
        this.transitions = ImmutableCreator.create(trans);
    }

    @Override
    public String getStrategyName() {
        throw new NotYetImplementedException(); //We can't process these (yet)
    }

    /** {@inheritDoc} */
    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new DefaultProofPurposeDescriptor(this, "Termination");
    }

    @Override
    public String export(final Export_Util o) {
        final StringBuilder res = new StringBuilder();

        final StringBuilder prevarSb = new StringBuilder();
        final StringBuilder postvarSb = new StringBuilder();
        boolean isFirst = true;
        for (final TRSVariable v : this.variables) {
            if (isFirst) {
                isFirst = false;
                prevarSb.append(v.toString());
                postvarSb.append(v.toString()).append("P");
            } else {
                prevarSb.append(", ").append(v.toString());
                postvarSb.append(", ").append(v.toString()).append("P");
            }
        }
        final String prevarString = prevarSb.toString();
        final String postvarString = postvarSb.toString();

        res.append("init([PC, ")
           .append(prevarString)
           .append("]) :- PC=")
           .append(this.startLoc.toString())
           .append(".")
           .append(o.cond_linebreak());
        res.append("next([PC, ")
           .append(prevarString)
           .append("], [PCP, ")
           .append(postvarString)
           .append("]) :-")
           .append(o.cond_linebreak());

        isFirst = true;
        for (final IntTransitionClause trans : this.transitions) {
            if (isFirst) {
                isFirst = false;
                res.append("        ");
                trans.export(o, res);
            } else {
                res.append(";").append(o.linebreak());
                res.append("        ");
                trans.export(o, res);
            }
        }
        res.append(".").append(o.linebreak());

        return res.toString();
    }
}

