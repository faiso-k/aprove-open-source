/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.itpf;

import aprove.verification.dpframework.IDPProblem.itpf.IItpfRule.*;
import immutables.*;


public interface IItpfVisitor {

    public boolean fcaseNeg(ItpfNeg neg);
    public Itpf caseNeg(ItpfNeg neg, Itpf newChild);
    public boolean fcaseItp(ItpfItp itp);
    public Itpf caseItp(ItpfItp itp);
    public boolean fcaseUra(ItpfUra ura);
    public Itpf caseUra(ItpfUra ura);
    public boolean fcaseAnd(ItpfAnd and);
    public Itpf caseAnd(ItpfAnd and, ImmutableSet<? extends Itpf> newChildren);
    public boolean fcaseOr(ItpfOr or);
    public Itpf caseOr(ItpfOr or, ImmutableSet<? extends Itpf> newChildren);
    public boolean fcaseAll(ItpfAll all);
    public Itpf caseAll(ItpfAll all, Itpf newChild);
    public boolean fcaseExists(ItpfExists exists);
    public Itpf caseExists(ItpfExists exists, Itpf newChild);
    public boolean fcaseTrue(ItpfTrue tru);
    public Itpf caseTrue(ItpfTrue tru);
    public boolean fcaseFalse(ItpfFalse fals);
    public Itpf caseFalse(ItpfFalse fals);


    public Itpf applyTo(Itpf c);

    public static abstract class ItpfVisitorSkeleton<MartkType extends Object> implements IItpfVisitor {

        protected final ItpfMark<MartkType> mark;
        protected final ApplicationMode mode;
        protected int applicationCount = 0;

        public ItpfVisitorSkeleton (final ItpfMark<MartkType> mark, final ApplicationMode mode) {
            this.mark = mark;
            this.mode = mode;
        }

        @Override
        public boolean fcaseNeg(final ItpfNeg neg) {
            return this.checkVisit(neg);
        }

        @Override
        public Itpf caseNeg(final ItpfNeg neg, final Itpf newChild){
            if (neg.getChild() != newChild) {
                final ItpfNeg res = ItpfNeg.create(newChild);
                neg.copyCompatibleMarks(res, this.mark);
                return this.mark(neg, res);
            } else {
                return this.mark(neg, neg);
            }
        }

        @Override
        public boolean fcaseItp(final ItpfItp itp){
            return this.checkVisit(itp);
        }

        @Override
        public Itpf caseItp(final ItpfItp itp){
            return this.mark(itp, itp);
        }

        @Override
        public boolean fcaseUra(final ItpfUra ura){
            return this.checkVisit(ura);
        }
        @Override
        public Itpf caseUra(final ItpfUra ura){
            return this.mark(ura, ura);
        }

        @Override
        public boolean fcaseAnd(final ItpfAnd and){
            return this.checkVisit(and);
        }
        @Override
        public Itpf caseAnd(final ItpfAnd and, final ImmutableSet<? extends Itpf> newChildren){
            if (and.getChildren() != newChildren) {
                final ItpfAnd res = ItpfAnd.create(newChildren);
                and.copyCompatibleMarks(res, this.mark);
                return this.mark(and, res);
            } else {
                return this.mark(and, and);
            }
        }

        @Override
        public boolean fcaseOr(final ItpfOr or){
            return this.checkVisit(or);
        }
        @Override
        public Itpf caseOr(final ItpfOr or, final ImmutableSet<? extends Itpf> newChildren){
            if (or.getChildren() != newChildren) {
                final ItpfOr res = ItpfOr.create(newChildren);
                or.copyCompatibleMarks(res, this.mark);
                return this.mark(or, res);
            } else {
                return this.mark(or, or);
            }
        }

        @Override
        public boolean fcaseAll(final ItpfAll all){
            return this.checkVisit(all);
        }

        @Override
        public Itpf caseAll(final ItpfAll all, final Itpf newChild){
            if (all.getChild() != newChild) {
                final ItpfAll res = ItpfAll.create(all.getVar(), newChild);
                all.copyCompatibleMarks(res, this.mark);
                return this.mark(all, res);
            } else {
                return this.mark(all, all);
            }
        }

        @Override
        public boolean fcaseExists(final ItpfExists exists){
            return this.checkVisit(exists);
        }
        @Override
        public Itpf caseExists(final ItpfExists exists, final Itpf newChild){
            if (exists.getChild() != newChild) {
                final ItpfExists res = ItpfExists.create(exists.getVar(), newChild);
                exists.copyCompatibleMarks(res, this.mark);
                return this.mark(exists, res);
            } else {
                return this.mark(exists, exists);
            }
        }

        @Override
        public boolean fcaseTrue(final ItpfTrue tru){
            return true;
        }
        @Override
        public Itpf caseTrue(final ItpfTrue tru){
            return tru;
        }

        @Override
        public boolean fcaseFalse(final ItpfFalse fals){
            return true;
        }
        @Override
        public Itpf caseFalse(final ItpfFalse fals){
            return fals;
        }

        @Override
        public Itpf applyTo(final Itpf c){
           return c.visit(this);
        }

        protected boolean checkVisit(final Itpf itpf) {
            return (this.applicationCount == 0 || this.mode != ApplicationMode.SingleStep) && !itpf.isMarked(this.mark);
        }

        protected Itpf mark(final Itpf origItpf, final Itpf newItpf) {
            if (origItpf == newItpf || this.mode == ApplicationMode.Multistep || newItpf.isAtom()) {
                newItpf.setMark(this.mark);
            }
            if (origItpf != newItpf) {
                origItpf.copyCompatibleMarks(newItpf, this.mark);
            }
            return newItpf;
        }
    }
}
