package aprove.verification.oldframework.CPF;

/**
 * Simple class which collects statistics when exporting a CPF proof.
 */
public class CPFExportStatistic {

    private int nrUnknownProofs = 0;
    private int nrRealProofs = 0;
    private int nrAssumptions = 0;

    @Override
    public String toString() {
        int total = this.nrRealProofs + this.nrUnknownProofs + this.nrAssumptions;
        return
        "Statistics for single proof: " +
        String.format("%3.2f", ((double)this.nrRealProofs * 100) / total)  + " % (" +
        this.nrRealProofs + " real / " +
        this.nrUnknownProofs + " unknown / " +
        this.nrAssumptions + " assumptions / " +
        total + " total proof steps)";
    }

    public void addUnknown() {
        this.nrUnknownProofs++;
    }

    public void addReal() {
        this.nrRealProofs++;
    }

    public void addAssumption() {
        this.nrAssumptions++;
    }

    public int getNrUnknownProofs() {
        return this.nrUnknownProofs;
    }

    public int getNrRealProofs() {
        return this.nrRealProofs;
    }

    public int getNrAssumptions() {
        return this.nrAssumptions;
    }
}
