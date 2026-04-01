package aprove.verification.complexity.LowerBounds.Types;

import aprove.prooftree.Export.Utility.*;


public class Type implements Exportable {

    public static final Type Nats = new Type("Nat");

    public static final Type Bool = new Type("Bool");

    public static final Type Unknown = new Type("Unknown");

    private String name;

    public Type(String name) {
        this.name = name;
    }

    @Override
    public String toString() {
        return this.name;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.name == null) ? 0 : this.name.hashCode());
        return result;
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
        Type other = (Type) obj;
        if (this.name == null) {
            if (other.name != null) {
                return false;
            }
        } else if (!this.name.equals(other.name)) {
            return false;
        }
        return true;
    }

    @Override
    public String export(Export_Util eu) {
        return eu.escape(this.name);
    }

}
