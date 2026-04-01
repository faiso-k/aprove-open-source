package aprove.input.Programs.xtc.tagHandler;

import aprove.input.Programs.xtc.*;
import aprove.input.Utility.XML.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import immutables.*;

public class PredefinedLogicalFunctionTag extends PredefinedFunctionTag {

    public PredefinedLogicalFunctionTag(XTCTagNames tag,
            Consumer<PredefinedFunction<? extends Domain>> parent) {
        super(parent, tag);
    }

    @Override
    public TagHandler<XTCTagNames> getSubHandler(XTCTagNames tag)
            throws IllegalArgumentException, UnsupportedOperationException {
        switch (tag) {
        case booleans:
            this.addDomain(DomainFactory.BOOLEAN);
            return new EmptyTag(tag);
        default:
            throw new IllegalSubTagException(this.tag.toString(),
                tag.toString());
        }
    }

    @Override
    public PredefinedFunction<? extends Domain> getResult() {
        switch (this.tag) {
        case logical_and:
            return (new PfConstructor() {
                @Override
                PredefinedFunction<? extends Domain> generate(ImmutableList<IntegerDomain> imIntDoms,
                        ImmutableList<BooleanDomain> imBoolDoms) {
                    return new PfLand(imBoolDoms);
                }
            }).getPf(PredefinedFunction.Func.Land, this.tag, this.domains);
        case logical_or:
            return (new PfConstructor() {
                @Override
                PredefinedFunction<? extends Domain> generate(ImmutableList<IntegerDomain> imIntDoms,
                        ImmutableList<BooleanDomain> imBoolDoms) {
                    return new PfLor(imBoolDoms);
                }
            }).getPf(PredefinedFunction.Func.Lor, this.tag, this.domains);
        case logical_not:
            return (new PfConstructor() {
                @Override
                PredefinedFunction<? extends Domain> generate(ImmutableList<IntegerDomain> imIntDoms,
                        ImmutableList<BooleanDomain> imBoolDoms) {
                    return new PfLnot(imBoolDoms);
                }
            }).getPf(PredefinedFunction.Func.Lnot, this.tag, this.domains);

        default:
            // unreachable, since tag must always be one of the preceeding arguments
            throw new RuntimeException();
        }
    }
}
