package aprove.verification.dpframework.DPConstraints;

public abstract class InRowSolutionIterator extends SolutionIterator {

    SolutionIterator[] solis;
    int position;
    int size;
    SolutionIterator currentSoli;

    public InRowSolutionIterator(int size) {
        super(null);
        this.position = 0;
        this.size = size;
        this.solis = new SolutionIterator[size];
    }

    public abstract SolutionIterator getSolutionIteratorFor(int pos);

    @Override
    public boolean isEmpty() {
        return this.size == 0;
    }

    @Override
    public boolean next() {
        if (this.loadPosition().next()) {
            do {
                if (this.nextPosition()) {
                    return true;
                }
            } while (this.loadPosition().isEmpty());
        }
        return false;
    }

    @Override
    public boolean extendWithCurrent(Solution sol) {
        if (this.size == 0) {
            sol.setNotValid();
            return false;
        }
        return sol.isValid() && this.loadPosition().extendWithCurrent(sol);
    }

    private boolean nextPosition() {
        this.position++;
        if (this.position == this.size) {
            this.position = 0;
            return true;
        }
        return false;
    }

    private SolutionIterator loadPosition() {
        this.currentSoli = this.solis[this.position];
        return (this.currentSoli == null) ? this.currentSoli =
            this.solis[this.position] = this.getSolutionIteratorFor(this.position) : this.currentSoli;
    }

}
