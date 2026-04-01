package aprove.verification.oldframework.Algebra.Terms;


/** This class visits two terms in parallel.
 */

public interface PairOfTermsVisitor {

    public abstract class PairsOfTermsVisitorSkeleton implements PairOfTermsVisitor {

        /** This class determines whether the left term is a variable
         *  or a function application. Then it tells this to a
         *  RightTermVisitor, which is then applied to the right Term.
         */
        private class LeftTermVisitor implements CoarseGrainedTermVisitor {

            AlgebraTerm rightTerm;

            @Override
            public Object caseVariable(AlgebraVariable v) {
                return this.rightTerm.apply(new RightTermVisitor(v));
            }

            @Override
            public Object caseFunctionApp(AlgebraFunctionApplication f) {
                return this.rightTerm.apply(new RightTermVisitor(f));
            }

            public LeftTermVisitor(AlgebraTerm rightTerm) {
                this.rightTerm = rightTerm;
            }

        }

        /** This class knows about the left term already, now determines
         *  what the right term is, and finally calls the appropriate
         *  PairOfTermsVisitor method.
         */
        private class RightTermVisitor implements CoarseGrainedTermVisitor {

            private AlgebraVariable leftTermVariable;
            private AlgebraFunctionApplication leftTermFunctionApp;

            @Override
            public Object caseVariable(AlgebraVariable v) {
                if (this.leftTermVariable != null) {
                    // left Term was a variable
                    return PairsOfTermsVisitorSkeleton.this.caseVarVar(this.leftTermVariable, v);
                }
                // left Term was a function app
                return PairsOfTermsVisitorSkeleton.this.caseFuncVar(this.leftTermFunctionApp, v);
            }

            @Override
            public Object caseFunctionApp(AlgebraFunctionApplication f) {
                if (this.leftTermVariable != null) {
                    // left Term was a variable
                    return PairsOfTermsVisitorSkeleton.this.caseVarFunc(this.leftTermVariable, f);
                }
                // left Term was a function app
                return PairsOfTermsVisitorSkeleton.this.caseFuncFunc(this.leftTermFunctionApp, f);
            }

            /** Left term was a variable.
             */
            public RightTermVisitor(AlgebraVariable v) {
                this.leftTermVariable = v;
                this.leftTermFunctionApp = null;
            }

            /** Left term was a function application.
             */
            public RightTermVisitor(AlgebraFunctionApplication f) {
                this.leftTermVariable = null;
                this.leftTermFunctionApp = f;
            }
        }

        /** Call this method to apply a PairOfTermsVisitor to a PairOfTerms.
         */
        final public Object applyToPair(PairOfTerms p) {
            return p.getLeft().apply(new LeftTermVisitor(p.getRight()));
        }

        /** Call this method to apply a PairOfTermsVisitor to two terms.
         */
        final public Object applyToPair(AlgebraTerm left, AlgebraTerm right) {
            return left.apply(new LeftTermVisitor(right));
        }

    }

    /** x, y case
     */
    public Object caseVarVar(AlgebraVariable x, AlgebraVariable y);

    /** x, g(...) case
     */
    public Object caseVarFunc(AlgebraVariable x, AlgebraFunctionApplication g);

    /** f(...), y case
     */
    public Object caseFuncVar(AlgebraFunctionApplication f, AlgebraVariable y);

    /** f(...) , g(...) case
     */
    public Object caseFuncFunc(AlgebraFunctionApplication f, AlgebraFunctionApplication g);

}

