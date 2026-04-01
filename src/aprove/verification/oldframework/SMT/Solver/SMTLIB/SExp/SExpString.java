package aprove.verification.oldframework.SMT.Solver.SMTLIB.SExp;

public class SExpString extends SExpAtom {

    private final String s;

    SExpString(String s) {
        this.s = s;
    }

    @Override
    public <T> T accept(SExpVisitor<T> visitor) {
        return visitor.visit(this);
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
        SExpString other = (SExpString) obj;
        if (this.s == null) {
            if (other.s != null) {
                return false;
            }
        } else if (!this.s.equals(other.s)) {
            return false;
        }
        return true;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + (this.s == null ? 0 : this.s.hashCode());
        return result;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append('"');
        for (int i = 0, l = this.s.length(); i < l; ++i) {
            char c = this.s.charAt(i);
            if (c == '\\' || c == '"') {
                sb.append('\\');
            }
            sb.append(c);
        }
        sb.append('"');
        return sb.toString();
    }
}
