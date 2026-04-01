package aprove.verification.oldframework.SMT.Solver.SMTLIB.SExp;

import java.io.*;

public abstract class SExpAtom extends SExp {
    @Override
    public void appendTo(Appendable app) throws IOException {
        app.append(this.toString());
    }

    @Override
    public SExp get(int i) {
        return null;
    }

    @Override
    public abstract String toString();
}
