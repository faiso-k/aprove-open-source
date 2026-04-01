package aprove.verification.dpframework.MCSProblem.mcnp;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;

/*
 * Stores two lists of arguments and the name
 */

public class ProgramPoint {

    private String _pointName;
    private Argument[] _arguments;
    private Set<Argument> _argumentsSet = new HashSet<Argument>();

    public ProgramPoint(String pointName, String[] arguments)
    {
        this._pointName=pointName;
        this._arguments = new Argument[arguments.length];
        for (int i=0; i<arguments.length; i++) {
            this._arguments[i] = new Argument(arguments[i]);
            this._argumentsSet.add(this._arguments[i]);
        }
    }

    public String getID() {
        return this._pointName+":"+this._arguments.length;
    }

    public String getPointName() {
        return this._pointName;
    }

    public Argument[] getArguments() {
        return this._arguments;
    }

    public Set<Argument> getArgumentsSet() {
        return this._argumentsSet;
    }

    // used in order to store Set of program points (automatic java usage)
    @Override
    public int hashCode()
    {
        return this.getID().hashCode();
    }

    @Override
    public boolean equals(Object other)
    {
        if (! (other instanceof ProgramPoint)) {
            return false;
        }
        return this.getID().equals(((ProgramPoint)other).getID());
    }

    @Override
    public String toString()
    {
        String res=this._pointName+"(";
        for (int i=0; i<this._arguments.length; i++) {
            res=res+this._arguments[i]+",";
        }
        res=res.substring(0,res.length()-1)+")";
        return res;
    }

    public TRSFunctionApplication toFunctionApplication() {
        int length = this._arguments.length;
        FunctionSymbol f = FunctionSymbol.create(this._pointName, length);
        ArrayList<TRSVariable> vars = new ArrayList<TRSVariable>(length);
        for (Argument arg : this._arguments) {
            vars.add(arg.toVariable());
        }
        TRSFunctionApplication res = TRSTerm.createFunctionApplication(f, vars);
        return res;
    }
}
