package aprove.verification.idpframework.Core.Utility.Marking;

import java.util.*;

import aprove.verification.idpframework.Processors.ItpfRules.*;
import aprove.verification.idpframework.Processors.ItpfRules.poly.*;

/**
 *
 * @author MP
 */
public enum CompatibleMarkClasses {

    I_UNIFY {
        final LinkedHashSet<Class<? extends Mark<?>>> COMPATBLE_CLASSES =
            new LinkedHashSet<Class<? extends Mark<?>>>() {{
                this.add(PolyRuleReachabilityToPoly.class);
                this.add(ItpfRelOp.class);
                this.add(PolyRuleRelOpToPoly.class);
                this.add(PolyRuleArithmeticToPoly.class);
                this.add(PolyRuleReachabilityToPoly.class);
                this.add(ItpRuleExpandDivModulo.class);
            }};

        @Override
        public boolean isCompatible(final Mark<?> mark) {
            return this.COMPATBLE_CLASSES.contains(mark.getClass());
        }
    },

    I_STEP_DETECT {
        final LinkedHashSet<Class<? extends Mark<?>>> COMPATBLE_CLASSES =
            new LinkedHashSet<Class<? extends Mark<?>>>() {{
                this.add(ItpfStepDetect.class);
                this.add(ItpfVarReduct.class);
                this.add(ItpfRelOp.class);
                this.add(PolyRuleRelOpToPoly.class);
                this.add(PolyRuleArithmeticToPoly.class);
                this.add(PolyRuleReachabilityToPoly.class);
                this.add(ItpRuleExpandDivModulo.class);
            }};

        @Override
        public boolean isCompatible(final Mark<?> mark) {
            return this.COMPATBLE_CLASSES.contains(mark.getClass());
        }
    },

    I_ROOT_CONSTRUCTOR {
        final LinkedHashSet<Class<? extends Mark<?>>> COMPATBLE_CLASSES =
            new LinkedHashSet<Class<? extends Mark<?>>>() {{
                this.add(ItpfRootConstr.class);
                this.add(ItpfStepDetect.class);
                this.add(ItpfVarReduct.class);
                this.add(ItpfRelOp.class);
                this.add(PolyRuleRelOpToPoly.class);
                this.add(PolyRuleArithmeticToPoly.class);
                this.add(PolyRuleReachabilityToPoly.class);
                this.add(ItpRuleExpandDivModulo.class);
            }};

        @Override
        public boolean isCompatible(final Mark<?> mark) {
            return this.COMPATBLE_CLASSES.contains(mark.getClass());
        }
    },

    I_BOOL_OP {
        final LinkedHashSet<Class<? extends Mark<?>>> COMPATBLE_CLASSES =
            new LinkedHashSet<Class<? extends Mark<?>>>() {{
                this.add(ItpfVarReduct.class);
                this.add(ItpfRelOp.class);
                this.add(PolyRuleRelOpToPoly.class);
                this.add(PolyRuleArithmeticToPoly.class);
                this.add(PolyRuleReachabilityToPoly.class);
                this.add(ItpRuleExpandDivModulo.class);
            }};

        @Override
        public boolean isCompatible(final Mark<?> mark) {
            return this.COMPATBLE_CLASSES.contains(mark.getClass());
        }
    },

    I_REWRITING {
        final LinkedHashSet<Class<? extends Mark<?>>> COMPATBLE_CLASSES =
            new LinkedHashSet<Class<? extends Mark<?>>>() {{
                this.add(ItpfStepDetect.class);
                this.add(ItpfRelOp.class);
                this.add(PolyRuleRelOpToPoly.class);
                this.add(PolyRuleArithmeticToPoly.class);
                this.add(PolyRuleReachabilityToPoly.class);
                this.add(ItpRuleExpandDivModulo.class);
            }};

        @Override
        public boolean isCompatible(final Mark<?> mark) {
            return this.COMPATBLE_CLASSES.contains(mark.getClass());
        }
    },

    I_TRIVIAL_IMPLICATION {
        final LinkedHashSet<Class<? extends Mark<?>>> COMPATBLE_CLASSES =
            new LinkedHashSet<Class<? extends Mark<?>>>() {{
                this.add(PolyRuleGCD.class);
            }};

        @Override
        public boolean isCompatible(final Mark<?> mark) {
            return this.COMPATBLE_CLASSES.contains(mark.getClass());
        }
    },


    P_GT_NORMALIZATION {
        final LinkedHashSet<Class<? extends Mark<?>>> COMPATBLE_CLASSES =
            new LinkedHashSet<Class<? extends Mark<?>>>() {{
                this.add(PolyRuleGCD.class);
            }};

        @Override
        public boolean isCompatible(final Mark<?> mark) {
            return this.COMPATBLE_CLASSES.contains(mark.getClass());
        }
    },

    P_GCD {
        final LinkedHashSet<Class<? extends Mark<?>>> COMPATBLE_CLASSES =
            new LinkedHashSet<Class<? extends Mark<?>>>() {{
            }};

        @Override
        public boolean isCompatible(final Mark<?> mark) {
            return this.COMPATBLE_CLASSES.contains(mark.getClass());
        }
    },

    POLY_RELATIONS {
        final LinkedHashSet<Class<? extends Mark<?>>> COMPATBLE_CLASSES =
            new LinkedHashSet<Class<? extends Mark<?>>>() {{
            }};

        @Override
        public boolean isCompatible(final Mark<?> mark) {
            return this.COMPATBLE_CLASSES.contains(mark.getClass());
        }
    },

    SOLVE_TRIVIAL_CONCLUSION {
        @Override
        public boolean isCompatible(final Mark<?> mark) {
            return false;
        }
    },

    REWRITE_TRANSITIVITY {
        @Override
        public boolean isCompatible(final Mark<?> mark) {
            // TODO Auto-generated method stub
            return false;
        }

    }, LoopUnroll {
        @Override
        public boolean isCompatible(final Mark<?> mark) {
            return false;
        }
    };

    public abstract boolean isCompatible(final Mark<?> mark);

}
