package aprove.verification.dpframework.Heuristics.Conditions;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.Heuristics.*;

public class RTIContains implements Condition {
    private final Metadata key;

    @ParamsViaArguments("key")
    public RTIContains(Metadata key) {
        this.key = key;
    }

    @Override
    public boolean check(BasicObligation obl, Abortion aborter, RuntimeInformation rti) {
        return rti.getMetadata(this.key) != null;
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return true;
    }

}
