package aprove.verification.dpframework.DPConstraints;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;

public interface TermAtom extends Constraint, HasTRSTerms, HasVariables, Atom {
    TRSTerm getLeft();

    TRSTerm getRight();

    TermAtom change(TRSTerm newLeft, TRSTerm newRight);

    public static abstract class TermAtomSkeleton extends Constraint.ConstraintSkeleton implements TermAtom {
        TRSTerm left;
        TRSTerm right;

        @Override
        public TRSTerm getLeft() {
            return this.left;
        }

        @Override
        public TRSTerm getRight() {
            return this.right;
        }

        @Override
        public boolean isAtom() {
            return true;
        }

        @Override
        public boolean isTermAtom() {
            return true;
        }

        public TermAtomSkeleton(TRSTerm left, TRSTerm right) {
            super();
            this.left = left;
            this.right = right;
        }

        private static FunctionSymbol getRootSymbolOf(TRSTerm t) {
            if (t.isVariable()) {
                return null;
            }
            return ((TRSFunctionApplication) t).getRootSymbol();
        }

        public FunctionSymbol getLeftRootSymbol() {
            return TermAtomSkeleton.getRootSymbolOf(this.left);
        }

        public FunctionSymbol getRightRootSymbol() {
            return TermAtomSkeleton.getRootSymbolOf(this.right);
        }

        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result + ((this.left == null) ? 0 : this.left.hashCode());
            result = prime * result + ((this.right == null) ? 0 : this.right.hashCode());
            return result;
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj) {
                return true;
            }
            if (obj == null) {
                return false;
            }
            if (this.getClass() != obj.getClass()) {
                return false;
            }
            final TermAtom.TermAtomSkeleton other = (TermAtom.TermAtomSkeleton) obj;
            if (this.left == null) {
                if (other.left != null) {
                    return false;
                }
            } else if (!this.left.equals(other.left)) {
                return false;
            }
            if (this.right == null) {
                if (other.right != null) {
                    return false;
                }
            } else if (!this.right.equals(other.right)) {
                return false;
            }
            return true;
        }

        /**
        public boolean collectUnifyProblemForImplication(Vector<Variable> yes,Vector<Variable> no,List<ConstraintUnifyProblem> cups, Constraint con, boolean multiSet) {
            if (!con.isAtom()) {
                cups.clear(); return false;
            }
            Atom atom = (Atom) con;
            return ConstraintUnifyProblem.addEquation(cups,this.getLeft(),atom.getLeft())
            && ConstraintUnifyProblem.addEquation(cups,this.getRight(),atom.getRight());
        }

        public boolean collectUnifyProblemForEquivalenz(List<ConstraintUnifyProblem> cups, Constraint con) {
            if (!con.isAtom()) {
                cups.clear(); return false;
            }
            Atom atom = (Atom) con;
            return ConstraintUnifyProblem.addEquation(cups,this.getLeft(),atom.getLeft())
            && ConstraintUnifyProblem.addEquation(cups,this.getRight(),atom.getRight());
        }
        **/

    }
}
