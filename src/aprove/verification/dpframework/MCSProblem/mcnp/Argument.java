package aprove.verification.dpframework.MCSProblem.mcnp;

import aprove.verification.dpframework.BasicStructures.*;

/*
 * Represent program point argument.
 * At the moment it just stores the argument name.
 * It is mostly for future use.
 */
public class Argument {

    private String _name;

    public Argument(String name)
    {
        this._name=name;
    }

    @Override
    public int hashCode()
    {
        return this._name.hashCode();
    }

    @Override
    public boolean equals(Object other)
    {
        if (! (other instanceof Argument)) {
            return false;
        }
        return this._name.equals(((Argument)other)._name);
    }

    @Override
    public String toString()
    {
        return this._name;
    }

    public TRSVariable toVariable() {
        return TRSTerm.createVariable(this._name);
    }
}
