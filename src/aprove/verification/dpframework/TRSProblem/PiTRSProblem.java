/*
 * Created on 11.04.2005
 */
package aprove.verification.dpframework.TRSProblem;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import immutables.*;

public final class PiTRSProblem extends AbstractPiTRSProblem {

    /**
     * creates a TRS problem.
     * @param R - the TRS
     * @param Q - the lhs's of Q where every term is in standard numbering
     */
    private PiTRSProblem(ImmutableSet<GeneralizedRule> R, ImmutableAfs Pi) {
        super("PiTRS", "PiTRS", R, Pi);
        if (Globals.useAssertions) {
            Rule.fromGeneralizedRules(Pi.filterGeneralizedRules(R));
        }
    }

    /**
     * creates a new TRS-Problem for the given collection of Rules,
     * Q will be empty
     * @param R_it
     */
    public static PiTRSProblem create(ImmutableSet<GeneralizedRule> R) {
        return PiTRSProblem.create(R, new ImmutableAfs(new Afs()));
    }


    /**
     * creates a new TRS-Problem for the given collection of Rules for R and Q
     * @param R_it
     * @param Q_it
     */
    public static PiTRSProblem create(ImmutableSet<GeneralizedRule> R, ImmutableAfs Pi) {
        return new PiTRSProblem(R, Pi);
    }

    /**
     * creates a sub problem with less rules in Q
     * @param rules
     * @return
     */
    public PiTRSProblem createSubProblem(ImmutableSet<GeneralizedRule> rules) {
        assert (this.getR().containsAll(rules));
        if (this.getR().size() == rules.size()) {
            if (Globals.DEBUG_NOWONDER || Globals.DEBUG_CRYINGSHADOW) {
                System.out.println("Warning: createSubProblem in PiTRS produces identity");
            }
            return this;
        }
        return new PiTRSProblem(rules, this.getPi());
    }

    @Override
    public String getName() {
        return "Pi-finite TRS";
    }

    @Override
    public String export(Export_Util o) {
        StringBuilder s = new StringBuilder();
        s.append(o.export("Pi-finite rewrite system:"));
        s.append(o.cond_linebreak());
        if (this.getR().isEmpty()) {
            s.append("R is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("The TRS R consists of the following rules:"));
            s.append(o.cond_linebreak());
            s.append(o.set(this.getR(), Export_Util.RULES));
            s.append(o.cond_linebreak());
        }

        if (this.getPi().isEmpty()) {
            s.append("Pi is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("The argument filtering Pi contains the following mapping:"));
            s.append(o.cond_linebreak());
            s.append(o.export(this.getPi()));
            s.append(o.cond_linebreak());
        }

        return s.toString();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getStrategyName() {
        return null;
    }
}
