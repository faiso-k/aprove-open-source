/*
 * Created on 11.04.2005
 */
package aprove.verification.dpframework.TRSProblem;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

public final class PPiTRSProblem extends AbstractPiTRSProblem {
    private final FunctionSymbol startSymbol;

    /**
     * creates a TRS problem.
     * @param R - the TRS
     * @param Q - the lhs's of Q where every term is in standard numbering
     */
    private PPiTRSProblem(ImmutableSet<GeneralizedRule> R, ImmutableAfs Pi,
            FunctionSymbol startSymbol) {
        super("PPiTRS", "Partial-Pi-TRS-Prolem", R, Pi);
        this.startSymbol = startSymbol;
    }

    /**
     * creates a new TRS-Problem for the given collection of Rules,
     * Q will be empty
     * @param R_it
     */
    public static PPiTRSProblem create(ImmutableSet<GeneralizedRule> R,
        FunctionSymbol startSymbol) {
        return PPiTRSProblem.create(R, new ImmutableAfs(new Afs()), startSymbol);
    }


    /**
     * creates a new TRS-Problem for the given collection of Rules for R and Q
     * @param R_it
     * @param Q_it
     */
    public static PPiTRSProblem create(ImmutableSet<GeneralizedRule> R,
        ImmutableAfs Pi,
        FunctionSymbol startSymbol) {
        return new PPiTRSProblem(R, Pi, startSymbol);
    }

    public FunctionSymbol getStartSymbol() {
        return this.startSymbol;
    }

    @Override
    public String getName() {
        return "partial Pi TRS";
    }

    @Override
    public String export(Export_Util o) {
        StringBuilder s = new StringBuilder();
        s.append(o.export("partial Pi rewrite system:"));
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
            s.append(o.export("The partial argument filtering Pi contains the following mapping:"));
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
