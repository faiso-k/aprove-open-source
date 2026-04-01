package aprove.input.Programs.Strategy;

public interface DeclarationVisitor {

    void visit(LetDeclaration letDeclaration);

    void visit(ClassDeclaration classDeclaration);

}
