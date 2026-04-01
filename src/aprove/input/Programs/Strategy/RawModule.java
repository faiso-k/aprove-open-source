package aprove.input.Programs.Strategy;

import java.io.*;
import java.util.*;
import java.util.Map.Entry;

/**
 * Captures the raw program structure of a parsed strategy module.
 */
public class RawModule implements VisitableStrategyElement {
    /**
     * Maps a module qualifier to a module name
     */
    final Map<String, String> imports =
        new LinkedHashMap<String, String>();

    /**
     * The namespace of this module.
     */
    final List<Declaration> namespace =
        new ArrayList<Declaration>();

    public List<Declaration> getNamespace() {
        return this.namespace;
    }

    public void addImport(String qualifier, String name) {
        this.imports.put(qualifier, name);
    }

    public void addDeclaration(Declaration decl) {
        this.namespace.add(decl);
    }

    public void addClassDecl(String name, String className, Parameters defaults) {
        if (defaults == null) {
            defaults = Parameters.EMPTY;
        }
        this.addDeclaration(new ClassDeclaration(name, className, defaults));
    }

    public void addLetDecl(String name, StrategyExpression body) {
        this.addDeclaration(new LetDeclaration(name, body));
    }

    public void print(Appendable ap) throws IOException {

        for (Entry<String, String> imp : this.imports.entrySet()) {
            String module = imp.getKey();
            String qualification = imp.getValue();
            if (module.equals(qualification)) {
                ap.append("import " + module + "\n");
            } else {
                ap.append("import " + module + " as " + qualification + "\n");
            }
        }

        ap.append("\n");

        for (Declaration d : this.namespace) {
            d.print(ap);
            ap.append("\n\n");
        }
    }

    @Override
    public void accept(StrategyElementVisitor visitor) {
        visitor.visit(this);
    }
}
