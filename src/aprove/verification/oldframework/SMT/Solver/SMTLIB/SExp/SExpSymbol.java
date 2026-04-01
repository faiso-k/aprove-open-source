package aprove.verification.oldframework.SMT.Solver.SMTLIB.SExp;

import aprove.*;

public class SExpSymbol extends SExpAtom {

    private String symbol;

    public SExpSymbol(String symbol) {
        if (Globals.useAssertions) {
            assert symbol.length() > 0;
            assert !SExpTokenizer.isDigit(symbol.charAt(0));
            for (char c : symbol.toCharArray()) {
                assert SExpTokenizer.isKeywordChar(c);
            }
        }
        this.symbol = symbol;
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
        SExpSymbol other = (SExpSymbol) obj;
        if (this.symbol == null) {
            if (other.symbol != null) {
                return false;
            }
        } else if (!this.symbol.equals(other.symbol)) {
            return false;
        }
        return true;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + (this.symbol == null ? 0 : this.symbol.hashCode());
        return result;
    }

    @Override
    public String toString() {
        return this.symbol;
    }
}
