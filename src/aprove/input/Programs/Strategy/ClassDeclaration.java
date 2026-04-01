/**
 *
 */
package aprove.input.Programs.Strategy;

import java.io.*;

public class ClassDeclaration extends Declaration {
    final String classname;
    final Parameters defaults;
    
    private final int hashCode;

    public ClassDeclaration(String name, String classname, Parameters defaults) {
        super(name);
        this.classname = classname;
        this.defaults = defaults;
        
        this.hashCode = this.classname.hashCode() * 17;
    }

    public String getClassname() {
        return this.classname;
    }

    public Parameters getDefaults() {
        return this.defaults;
    }

    @Override
    public void print(Appendable ap) throws IOException {
        PrettyPrintState pps = new PrettyPrintState();
        pps.append(ap, "declare " + this.name + " = " + this.classname);
        if (this.defaults != null && ! this.defaults.params.isEmpty()) {
            pps.newLine(ap);
            pps.indentMore();
            pps.indent(ap);
            pps.append(ap, "defaults ");
            this.defaults.print(ap, pps);
        }
    }

    @Override
    public String toString() {
        StringBuilder builder = new StringBuilder();
        builder.append("declare ");
        builder.append(this.name);
        builder.append(" = ");
        builder.append(this.classname);
        if (this.defaults != null && ! this.defaults.params.isEmpty()) {
            builder.append("\n    defaults ");
            this.defaults.toBuilder(builder);
        }
        return builder.toString();
    }
    
    @Override
    public int hashCode() {
        return hashCode;
    }

    @Override
    public boolean equals(Object obj) {
        if (! (obj instanceof ClassDeclaration)) {
            return false;
        }
        ClassDeclaration other = (ClassDeclaration) obj;
        return this.name.equals(other.name) &&
                this.classname.equals(other.classname) &&
                this.defaults.equals(other.defaults);
    }
    @Override
    public void accept(DeclarationVisitor visitor) {
        visitor.visit(this);
    }
}