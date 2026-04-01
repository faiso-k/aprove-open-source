package aprove.input.Programs.prolog;

import aprove.*;
import aprove.input.Programs.prolog.structure.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import immutables.*;

/**
 * A Query contains a name of a predicate and the moding for this
 * predicate for termination analysis.<br><br>
 *
 * Created: Sep 7, 2006<br>
 * Last modified: Oct 7, 2006
 *
 * @author cryingshadow
 * @version $Id$
 */
public class PrologQuery implements Exportable, Immutable {

    /**
     * The moding. Also specifies the arity by the length of the array.
     */
    private final Moding[] mode;

    /**
     * The name of the predicate.
     */
    private final String name;

    /**
     * What do we analyze this class of queries for?
     */
    private final PrologPurpose purpose;

    /**
     * Constructs a new termination Query with a predicate specified by its
     * FunctionSymbol and a moding which sets all arguments of the
     * predicate to be ground.
     * @param f The predicate's FunctionSymbol.
     */
    public PrologQuery(FunctionSymbol f) {
        this(f.getName(), f.getArity(), PrologPurpose.TERMINATION);
    }

    /**
     * Constructs a new Query with a predicate specified by the given name and the arity being equal to the
     * length of the given array. The moding is constructed from the array where TRUE entries specify ground arguments.
     * @param nameParam The name of the predicate.
     * @param moding The moding (and arity).
     * @param p The purpose of this query.
     */
    public PrologQuery(String nameParam, Boolean[] moding, PrologPurpose p) {
        this(nameParam, PrologQuery.transformToModing(moding), p);
    }

    /**
     * Constructs a new Query with a predicate specified by its name and
     * arity and a moding which sets all arguments of the predicate to be
     * ground.
     * @param n The predicate's name.
     * @param arity The predicate's arity.
     * @param p The purpose of this query.
     */
    public PrologQuery(String n, int arity, PrologPurpose p) {
        if (Globals.useAssertions) {
            assert (arity >= 0) : "Arity must not be negative!";
            assert (n != null && !"".equals(n)) : "Name must not be empty!";
        }
        this.name = n;
        this.mode = new Moding[arity];
        for (int i = 0; i < arity; i++) {
            this.mode[i] = Moding.GROUND;
        }
        this.purpose = p;
    }

    /**
     * Constructs a new Query with the specified name and moding.
     * @param n The predicate's name.
     * @param m The predicate's moding. Its size must match the
     *          predicate's arity.
     * @param p The purpose of this query.
     */
    public PrologQuery(String n, Moding[] m, PrologPurpose p) {
        if (Globals.useAssertions) {
            assert (n != null && !"".equals(n)) : "Name must not be empty!";
        }
        this.name = n;
        this.mode = m;
        this.purpose = p;
    }

    /**
     * Constructs a new Query with the specified name and moding.
     * @param n The predicate's name.
     * @param m The predicate's moding. Its size must match the
     *          predicate's arity.
     * @param p The purpose of this query.
     */
    public PrologQuery(String n, YNM[] m, PrologPurpose p) {
        this(n, PrologQuery.transformToModing(m), p);
    }

    /**
     * Transforms a Boolean array to a Moding array where True entries are converted to GROUND entries.
     * @param moding The moding.
     * @return A Moding array specifying the same moding.
     */
    private static Moding[] transformToModing(Boolean[] moding) {
        Moding[] res = new Moding[moding.length];
        for (int i = 0; i < res.length; i++) {
            res[i] = moding[i] ? Moding.GROUND : Moding.ANY;
        }
        return res;
    }

    /**
     * Transforms a YNM array to a Moding array where YES entries are converted to GROUND entries.
     * @param m The moding.
     * @return A Moding array specifying the same moding.
     */
    private static Moding[] transformToModing(YNM[] m) {
        Moding[] res = new Moding[m.length];
        for (int i = 0; i < res.length; i++) {
            res[i] = m[i] == YNM.YES ? Moding.GROUND : Moding.ANY;
        }
        return res;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object o) {
        if (o instanceof PrologQuery) {
            PrologQuery q = (PrologQuery) o;
            if (q.getName().equals(this.getName()) && q.getModing().length == this.getModing().length) {
                boolean res = true;
                for (int i = 0; i < this.getModing().length; i++) {
                    res &= q.getModing()[i].equals(this.getModing()[i]);
                }
                return res;
            }
        }
        return false;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Utility.Exportable#export(aprove.verification.oldframework.Utility.Export_Util)
     */
    @Override
    public String export(Export_Util o) {
        return o.export(this.toString());
        //TODO the following is the old HTML export - maybe use this?
        //        StringBuilder res = new StringBuilder();
        //        res.append(this.getName());
        //        res.append("(");
        //        if (this.getModing() != null && this.getArity() > 0) {
        //            res.append(this.getModing()[0] == YNM.YES ? "<font color=blue>g</font>" : "<font color=red>a</font>");
        //            for (int i = 1; i < this.getArity(); i++) {
        //                res.append(",");
        //                res.append(this.getModing()[i] == YNM.YES ? "<font color=blue>g</font>" : "<font color=red>a</font>");
        //            }
        //        }
        //        res.append(")");
        //        return res.toString();
    }

    /**
     * Returns the query's arity.
     * @return The query's arity.
     */
    public int getArity() {
        return this.getModing().length;
    }

    /**
     * Returns the moding.
     * @return The moding.
     */
    public Moding[] getModing() {
        return this.mode;
    }

    /**
     * Returns the moding as YNM array where numbers are treated as ground terms.
     * @return The moding as YNM array.
     */
    public YNM[] getModingAsAfs() {
        YNM[] res = new YNM[this.mode.length];
        for (int i = 0; i < this.mode.length; i++) {
            switch (this.mode[i]) {
            case GROUND:
            case NUMBER:
                res[i] = YNM.YES;
                break;
            default:
                res[i] = YNM.NO;
            }
        }
        return res;
    }

    /**
     * Returns the name.
     * @return The name.
     */
    public String getName() {
        return this.name;
    }

    /**
     * @return The purpose.
     */
    public PrologPurpose getPurpose() {
        return this.purpose;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        int res = this.getName().hashCode();
        for (Moding item : this.getModing()) {
            res += item.hashCode();
        }
        return res;
    }

    /**
     * @param p The new purpose.
     * @return A new query with the same predicate and moding, but the new purpose.
     */
    public PrologQuery setPurpose(PrologPurpose p) {
        if (Globals.useAssertions) {
            assert (p != null) : "Purpose may not be null!";
        }
        return new PrologQuery(this.name, this.mode, p);
    }

    /**
     * Returns a new Query with the same predicate name, but with the specified moding (if the arities match each
     * other).
     * @param info The new moding.
     * @return A new Query with the specified moding.
     */
    public PrologQuery setQueryModing(Moding[] info) {
        if (info == null) {
            throw new NullPointerException();
        }
        if (info.length != this.getArity()) {
            throw new IllegalArgumentException("Arity does not match!");
        }
        return new PrologQuery(this.getName(), info, this.getPurpose());
    }

    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        StringBuilder res = new StringBuilder();
        res.append(this.getName());
        res.append("(");
        if (this.getModing() != null && this.getArity() > 0) {
            res.append(this.getModing()[0].toString());
            for (int i = 1; i < this.getArity(); i++) {
                res.append(",");
                res.append(this.getModing()[i].toString());
            }
        }
        res.append(")");
        return res.toString();
    }

}
