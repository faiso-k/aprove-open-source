/**
 *
 */
package aprove.input.Programs.Strategy;

import java.io.*;

abstract class Declaration {
    final String name;
    Declaration(String name) {
        this.name = name;
    }

    public abstract void accept(DeclarationVisitor visitor);

    public abstract void print(Appendable ap) throws IOException;
}