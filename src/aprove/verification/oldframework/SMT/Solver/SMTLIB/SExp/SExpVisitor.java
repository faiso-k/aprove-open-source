package aprove.verification.oldframework.SMT.Solver.SMTLIB.SExp;

public interface SExpVisitor<T> {

    public T visit(SExpBinary sExpBinary);

    public T visit(SExpDecimal sExpDecimal);

    public T visit(SExpKeyword sExpKeyword);

    public T visit(SExpList sExpList);

    public T visit(SExpNumeral sExpNumeral);

    public T visit(SExpString sExpString);

    public T visit(SExpSymbol sExpSymbol);

}
