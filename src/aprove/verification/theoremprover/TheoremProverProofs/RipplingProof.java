/*
 * Created on 28.09.2004
 */
package aprove.verification.theoremprover.TheoremProverProofs;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Rippling.*;
import aprove.verification.theoremprover.TerminationProofs.*;
import aprove.verification.theoremprover.TheoremProverProcedures.*;

/**
 * @author rabe
 */
public class RipplingProof extends TheoremProverProof {

    protected RipplingProcessor.Direction direction;

    protected Formula        oldFormula;
    protected Formula        newFormula;

    protected Set<WaveRule> waveRules;
    protected Formula          annotatedConclusion;

    public RipplingProof(RipplingProcessor.Direction direction, Formula oldFormula, Formula newFormula, Set<WaveRule> waveRules,
            Formula annotatedConclustion) {

        this.name         = "Rippling "+(direction == RipplingProcessor.Direction.In ? "In" : "Out");
        this.shortName     = this.name;
        this.longName      = this.name;

        this.direction  = direction;
        this.newFormula = newFormula;
        this.oldFormula = oldFormula;

        this.waveRules = waveRules;
        this.annotatedConclusion = annotatedConclustion;
    }


    @Override
    public String export(Export_Util o) {
        StringBuffer output = new StringBuffer();

        output.append(o.export(this.oldFormula));
        output.append(o.bold(" could be rippled to "));
        output.append(o.export(this.newFormula));

        output.append(o.linebreak());
        output.append(o.linebreak());

        output.append( o.bold("Generated Wave-Rules:"));
        output.append(o.linebreak());
        for(WaveRule waveRule : this.waveRules) {
            output.append(o.export(waveRule));
            output.append(o.linebreak());
        }

        output.append(o.linebreak());
        output.append(o.bold("Annotated conclusion:"));
        output.append(o.linebreak());
        output.append(o.export(this.annotatedConclusion));

        return output.toString();
    }

    public String toBibTeX() {
        return null;
    }

    @Override
    public Proof deepcopy() {
        Set<WaveRule> rules = new LinkedHashSet<WaveRule>();
        for(WaveRule waveRule : this.waveRules) {
            rules.add(waveRule.deepcopy());
        }

        return new RipplingProof(this.direction,this.oldFormula.deepcopy(),this.newFormula.deepcopy(),rules, this.annotatedConclusion.deepcopy());
    }

}
