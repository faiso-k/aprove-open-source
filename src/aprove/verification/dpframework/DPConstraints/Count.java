package aprove.verification.dpframework.DPConstraints;

public class Count {
    public final int induction;
    public final int depth;
    public final int rewriting;

    public Count() {
        this.induction = 0;
        this.depth = 0;
        this.rewriting = 0;
    }

    public Count(final int induction, final int depth, final int rewriting) {
        super();
        this.induction = induction;
        this.depth = depth;
        this.rewriting = rewriting;
    }

    public Count incInduction() {
        return new Count(this.getInduction() + 1, this.getDepth(), this.rewriting);
    }

    public Count incDepth() {
        return new Count(this.getInduction(), this.getDepth() + 1, this.rewriting);
    }

    public Count incRewriting() {
        return new Count(this.getInduction(), this.getDepth(), this.rewriting + 1);
    }

    public int getDepth() {
        return this.depth;
    }

    public int getInduction() {
        return this.induction;
    }

    public int getRewriting() {
        return this.rewriting;
    }

    @Override
    public String toString() {
        return this.induction + "." + this.depth + " /" + this.rewriting;
    }

    public boolean greaterThan(Count count) {
        if (this.getInduction() > count.getInduction()) {
            return true;
        }
        if (this.getInduction() < count.getInduction()) {
            return false;
        }
        return this.getDepth() > count.getDepth();
    }

    public boolean isRewritingGreaterThan(Count count) {
        return this.induction > count.induction;
    }
}
