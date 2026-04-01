package aprove.input.Programs.xtc.tagHandler;

import aprove.input.Programs.xtc.*;
import aprove.input.Utility.XML.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import immutables.*;

public class PredefinedArithmeticFunctionTag extends PredefinedFunctionTag {

    public PredefinedArithmeticFunctionTag(XTCTagNames tag,
            Consumer<PredefinedFunction<? extends Domain>> parent) {
        super(parent, tag);
    }

    @Override
    public TagHandler<XTCTagNames> getSubHandler(XTCTagNames tag)
            throws IllegalArgumentException, UnsupportedOperationException {
        switch (tag) {
        case integers:
            this.addDomain(DomainFactory.INTEGERS);
            return new EmptyTag(tag);
        case naturals:
            throw new IllegalArgumentException(
                "Domain naturals not yet supported.");
        default:
            throw new IllegalSubTagException(this.tag.toString(),
                tag.toString());
        }
    }

    @Override
    public PredefinedFunction<? extends Domain> getResult() {
        switch (this.tag) {
        case cast:
            return (new PfConstructor() {
                @Override
                PredefinedFunction<? extends Domain> generate(ImmutableList<IntegerDomain> imIntDoms,
                        ImmutableList<BooleanDomain> imBoolDoms) {
                    return new PfCast(imIntDoms);
                }
            }).getPf(PredefinedFunction.Func.Cast, this.tag, this.domains);
        case plus:
            return (new PfConstructor() {
                @Override
                PredefinedFunction<? extends Domain> generate(ImmutableList<IntegerDomain> imIntDoms,
                        ImmutableList<BooleanDomain> imBoolDoms) {
                    return new PfAdd(imIntDoms);
                }
            }).getPf(PredefinedFunction.Func.Add, this.tag, this.domains);
        case minus:
            return (new PfConstructor() {
                @Override
                PredefinedFunction<? extends Domain> generate(ImmutableList<IntegerDomain> imIntDoms,
                        ImmutableList<BooleanDomain> imBoolDoms) {
                    return new PfSub(imIntDoms);
                }
            }).getPf(PredefinedFunction.Func.Sub, this.tag, this.domains);
        case u_minus:
            return (new PfConstructor() {
                @Override
                PredefinedFunction<? extends Domain> generate(ImmutableList<IntegerDomain> imIntDoms,
                        ImmutableList<BooleanDomain> imBoolDoms) {
                    return new PfUnaryMinus(imIntDoms);
                }
            }).getPf(PredefinedFunction.Func.UnaryMinus, this.tag, this.domains);
        case times:
            return (new PfConstructor() {
                @Override
                PredefinedFunction<? extends Domain> generate(ImmutableList<IntegerDomain> imIntDoms,
                        ImmutableList<BooleanDomain> imBoolDoms) {
                    return new PfMul(imIntDoms);
                }
            }).getPf(PredefinedFunction.Func.Mul, this.tag, this.domains);
        case div:
            return (new PfConstructor() {
                @Override
                PredefinedFunction<? extends Domain> generate(ImmutableList<IntegerDomain> imIntDoms,
                        ImmutableList<BooleanDomain> imBoolDoms) {
                    return new PfDiv(imIntDoms);
                }
            }).getPf(PredefinedFunction.Func.Div, this.tag, this.domains);
        case modulo:
            return (new PfConstructor() {
                @Override
                PredefinedFunction<? extends Domain> generate(ImmutableList<IntegerDomain> imIntDoms,
                        ImmutableList<BooleanDomain> imBoolDoms) {
                    return new PfMod(imIntDoms);
                }
            }).getPf(PredefinedFunction.Func.Mod, this.tag, this.domains);
        case greater_than:
            return (new PfConstructor() {
                @Override
                PredefinedFunction<? extends Domain> generate(ImmutableList<IntegerDomain> imIntDoms,
                        ImmutableList<BooleanDomain> imBoolDoms) {
                    return new PfGt(imIntDoms);
                }
            }).getPf(PredefinedFunction.Func.Gt, this.tag, this.domains);
        case greater_equals:
            return (new PfConstructor() {
                @Override
                PredefinedFunction<? extends Domain> generate(ImmutableList<IntegerDomain> imIntDoms,
                        ImmutableList<BooleanDomain> imBoolDoms) {
                    return new PfGe(imIntDoms);
                }
            }).getPf(PredefinedFunction.Func.Ge, this.tag, this.domains);
        case less_than:
            return (new PfConstructor() {
                @Override
                PredefinedFunction<? extends Domain> generate(ImmutableList<IntegerDomain> imIntDoms,
                        ImmutableList<BooleanDomain> imBoolDoms) {
                    return new PfLt(imIntDoms);
                }
            }).getPf(PredefinedFunction.Func.Lt, this.tag, this.domains);
        case less_equals:
            return (new PfConstructor() {
                @Override
                PredefinedFunction<? extends Domain> generate(ImmutableList<IntegerDomain> imIntDoms,
                        ImmutableList<BooleanDomain> imBoolDoms) {
                    return new PfLe(imIntDoms);
                }
            }).getPf(PredefinedFunction.Func.Le, this.tag, this.domains);
        case equals:
            return (new PfConstructor() {
                @Override
                PredefinedFunction<? extends Domain> generate(ImmutableList<IntegerDomain> imIntDoms,
                        ImmutableList<BooleanDomain> imBoolDoms) {
                    return new PfEq(imIntDoms);
                }
            }).getPf(PredefinedFunction.Func.Eq, this.tag, this.domains);
        case not_equals:
            return (new PfConstructor() {
                @Override
                PredefinedFunction<? extends Domain> generate(ImmutableList<IntegerDomain> imIntDoms,
                        ImmutableList<BooleanDomain> imBoolDoms) {
                    return new PfNeq(imIntDoms);
                }
            }).getPf(PredefinedFunction.Func.Neq, this.tag, this.domains);
        default:
            // unreachable, since tag must always be one of the preceeding arguments
            throw new RuntimeException();
        }
    }
}
