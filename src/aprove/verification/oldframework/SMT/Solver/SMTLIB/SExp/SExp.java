package aprove.verification.oldframework.SMT.Solver.SMTLIB.SExp;

import java.io.*;

public abstract class SExp {

    public abstract <T> T accept(SExpVisitor<T> visitor);

    public abstract void appendTo(Appendable app) throws IOException;

    public abstract SExp get(int i);

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        try {
            this.appendTo(sb);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        return sb.toString();
    }
}
