package aprove.strategies.ExecutableStrategies;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Start a processor and get its result.
 * If run with low priority it may result in a not started fail.
 */
public class ExecProcessorStrategy extends ExecutableStrategy {

    private final class DiscardedProcessorProof extends Proof.DefaultProof {
        private final ExecutableStrategy strResult;
        public DiscardedProcessorProof(ExecutableStrategy strResult) {
            this.strResult = strResult;
            this.shortName = "discarded " + this.shortName;
            this.longName = "Discarded " + this.shortName + ExecProcessorStrategy.this.nameAddendum;
        }
        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return "This processor was applied here, but was not successful. " +
                    "It was terminated or failed, producing " + this.strResult;
        }
    }

    private final Processor proc;
    private final BasicObligationNode obl;
    private final String shortName;
    private final String nameAddendum;
    private Executor executor;

    public ExecProcessorStrategy(Processor p, BasicObligationNode obl, RuntimeInformation rti,
            String shortName, String nameAddendum) {
        super(rti);
        this.obl = obl;
        this.proc = p;
        this.shortName = shortName;
        this.nameAddendum = nameAddendum;
        this.executor = null;
    }

    @Override
    ExecutableStrategy exec() {
        if (this.executor == null) {
            BasicObligation bobl = this.obl.getBasicObligation();
            if (this.proc.isApplicable(bobl)) {
                this.executor = new Executor(this.obl, this.proc, this.rti, this.shortName, this.nameAddendum);
                this.executor.start();
                return null;
            } else {
                return this.finish(ResultFactory.notApplicable());
            }
        }

        Result res = this.executor.getResult();
        if (res != null) {
            return this.finish(res);
        } else {
            return null;
        }
    }

    public ExecutableStrategy finish(Result res) {
        if (Globals.FULL_PROOF_TREE && res.getObligationChild() == null) {
            // debug output - create NO node behind SOUND to carry our "fail" proof
            List<ObligationNode> empty = Collections.<ObligationNode>emptyList();
            Proof proof = new DiscardedProcessorProof(res.getStrategy());
            YNMImplication impl = YNMImplication.SOUND;

            // And adjust the Result to include the new child.
            res = ResultFactory.provedOrWithNewStrategy(empty,
                    impl, proof, res.getStrategy());
        }
        // Execute the result. execute it immediately, so this method behaves
        // exactly like it did before ExecResult was introduced.
        return new ExecResult(this.rti, this.obl, res).exec();
    }

    @Override
    void stop(String reason) {
        if (this.executor != null) {
            this.executor.stop(reason);
        }
    }

    @Override
    public String toString() {
        return "EProc("+this.shortName+", "+"someObl"+")";
    }


}
