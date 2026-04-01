package aprove.verification.oldframework.SMT.Solver.SMTLIB.SExp;

import java.io.*;
import java.util.*;

import immutables.*;

public class SExpList extends SExp {
    private final ImmutableList<SExp> args;

    public SExpList(ImmutableList<SExp> args) {
        this.args = args;
    }

    public SExpList(SExp... args) {
        this(ImmutableCreator.create(new ArrayList<>(Arrays.asList(args))));
    }

    @Override
    public <T> T accept(SExpVisitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public void appendTo(Appendable app) throws IOException {
        app.append('(');
        boolean first = true;
        for (SExp a : this.getArgs()) {
            if (first) {
                first = false;
            } else {
                app.append(' ');
            }
            if (app == null) {
                assert false;
            }
            a.appendTo(app);
        }
        app.append(')');
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
        SExpList other = (SExpList) obj;
        if (this.args == null) {
            if (other.args != null) {
                return false;
            }
        } else if (!this.args.equals(other.args)) {
            return false;
        }
        return true;
    }

    @Override
    public SExp get(int i) {
        return this.args.get(i);
    }

    public ImmutableList<SExp> getArgs() {
        return this.args;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + (this.args == null ? 0 : this.args.hashCode());
        return result;
    }

}
