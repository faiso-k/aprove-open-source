/*
 * Created on Jan 23, 2006
 */
package aprove.verification.dpframework.BasicStructures.Unification.Equational.Utility;

import java.util.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * An ACnCTerm is a term representation where the AC arguments are flattened
 * and put together with the C arguments into a multiset, so nested AC symbols
 * will be dropped and the AC Symbols will have variable arity.
 * Needed for AC unification.
 *
 * @author Stephan Falke
 * @version $Id$
 */


public class ACnCTerm implements Immutable{

    private TRSTerm term; // term representation of this ACTerm
    private MultisetOfACnCTerms multiargs; //args represented as a multiset, if fSymb is AC or C
    private boolean hasMultiargs;
    private ImmutableArrayList<ACnCTerm> args;
    private boolean hasArgs;
    private FunctionSymbol fSymb; //the outer FunctionSymbol or null if this term is a Variable
    private ImmutableArrayList<FunctionSymbol> acFs; //FunctionSymbols that are AC
    private ImmutableArrayList<FunctionSymbol> cFs; //FunctionSymbols that are C and not A


    private ACnCTerm(FunctionSymbol f, ArrayList<ACnCTerm> args, Collection<FunctionSymbol> acFs, Collection<FunctionSymbol> cFs) {
        this.multiargs = null;
        this.args = ImmutableCreator.create(args);
        this.hasArgs = true;
        this.hasMultiargs = false;

        this.acFs = ImmutableCreator.create(new ArrayList<FunctionSymbol>(acFs));
        this.cFs =  ImmutableCreator.create(new ArrayList<FunctionSymbol>(cFs));
        this.fSymb = f;
        this.term = this.constructTerm();
    }

    private ACnCTerm(FunctionSymbol f, MultisetOfACnCTerms multiargs, Collection<FunctionSymbol> acFs, Collection<FunctionSymbol> cFs) {
        this.multiargs = multiargs;
        this.args = null;
        this.hasArgs = false;
        this.hasMultiargs = true;

        this.acFs = ImmutableCreator.create(new ArrayList<FunctionSymbol>(acFs));
        this.cFs =  ImmutableCreator.create(new ArrayList<FunctionSymbol>(cFs));
        this.fSymb = f;
        this.term = this.constructTerm();
    }

    /*
     * Calculates this.term - fSymb must be given
     */
    private TRSTerm constructTerm() {
        if(Globals.useAssertions) {
            assert this.fSymb != null;
        }
        if(this.hasArgs) {
            ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>();
            for(ACnCTerm i : this.args) {
                newArgs.add(i.toTerm());
            }
            return TRSTerm.createFunctionApplication(this.fSymb, ImmutableCreator.create(newArgs));
        }
        else {
            ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>();
            for(ACnCTerm s : this.multiargs.toTermArrayList()) {
                TRSTerm ss = s.toTerm();
                int n = this.multiargs.numberOfOccurences(s);
                for(int i=0; i<n; i++) {
                    newArgs.add(ss);
                }
            }
            /* deflatten */
            /* newArgs has >= arity elements */
            return this.deflatten(newArgs);
        }
    }

    /**
     * Deflattens the given Term, e.g. introduces the function symbols again with the real arity.
     */
    private TRSTerm deflatten(ArrayList<TRSTerm> args) {
        ArrayList<TRSTerm> resArgs = new ArrayList<TRSTerm>();
        if(Globals.useAssertions) {
            assert this.fSymb != null;
        }
        int n = this.fSymb.getArity();
        if(args.size()==n) {
            for(int i=0; i<n; i++) {
                resArgs.add(args.get(i));
            }
        }
        else {
            for(int i=0; i<n-1; i++) {
                resArgs.add(args.get(i));
                args.remove(i);
            }
            resArgs.add(this.deflatten(args));
        }
        return TRSTerm.createFunctionApplication(this.fSymb, ImmutableCreator.create(resArgs));
    }

    private ACnCTerm(TRSTerm t, Collection<FunctionSymbol> acFs, Collection<FunctionSymbol> cFs) {
        this.multiargs = null;
        this.args = null;
        this.hasArgs = false;
        this.hasMultiargs = false;

        this.term = t;
        this.acFs = ImmutableCreator.create(new ArrayList<FunctionSymbol>(acFs));
        this.cFs = ImmutableCreator.create(new ArrayList<FunctionSymbol>(cFs));

        if(t.isVariable()) {
            return;
        }
        else {
            this.fSymb = ((TRSFunctionApplication)t).getRootSymbol();
            if(acFs.contains(this.fSymb) || cFs.contains(this.fSymb)) {
                this.hasMultiargs = true;
                ArrayList<ACnCTerm> multiVec = new ArrayList<ACnCTerm>();
                for(TRSTerm i : ((TRSFunctionApplication)t).getArguments()) {
                    ACnCTerm s = ACnCTerm.create(i, acFs, cFs);
                    if(!(i instanceof TRSVariable) && s.fSymb.equals(this.fSymb) && acFs.contains(this.fSymb)) {
                        multiVec.addAll(s.multiargs.toRealTermArrayList());
                    }
                    else {
                        multiVec.add(s);
                    }
                }
                this.multiargs = MultisetOfACnCTerms.create(multiVec);
            }
            else {
                this.hasArgs = true;
                ArrayList<ACnCTerm> args = new ArrayList<ACnCTerm>();
                for(TRSTerm i : ((TRSFunctionApplication)t).getArguments()) {
                    args.add(ACnCTerm.create(i, acFs, cFs));
                }
                this.args = ImmutableCreator.create(args);
            }
        }
    }

    /** Returns a new instance of <code>ACnCTerm</code>.
     * @param t   the term that's to be transformed into an ACnCTerm
     * @param Fac   the AC symbols
     * @param Fc   the C symbols
     */
    public static ACnCTerm create(TRSTerm t, Collection<FunctionSymbol> Fac, Collection<FunctionSymbol> Fc) {
        return new ACnCTerm(t, Fac, Fc);
    }

    /** Returns a new instance of <code>ACnCTerm</code>.
     * @param f     the head function symbol
     * @param args  the arguments
     * @param Fac   the AC symbols
     * @param Fc   the C symbols
     */
    public static ACnCTerm create(FunctionSymbol f, ArrayList<ACnCTerm> args, Collection<FunctionSymbol> Fac, Collection<FunctionSymbol> Fc) {
        return new ACnCTerm(f, args, Fac, Fc);
    }

    /** Returns a new instance of <code>ACnCTerm</code>.
     * @param f     the head function symbol
     * @param multiargs  the arguments
     * @param Fac   the AC symbols
     * @param Fc   the C symbols
     */
    public static ACnCTerm create(FunctionSymbol f, MultisetOfACnCTerms multiargs, Collection<FunctionSymbol> Fac, Collection<FunctionSymbol> Fc) {
        return new ACnCTerm(f, multiargs, Fac, Fc);
    }

    public Collection<FunctionSymbol> getAcFs() {
        return this.acFs;
    }

    public Collection<FunctionSymbol> getCFs() {
        return this.cFs;
    }

    public boolean isVariable() {
        return this.term.isVariable();
    }

    public boolean isConstant() {
        if(!(this.fSymb instanceof FunctionSymbol)) {
            return false;
        }
        else {
            return ((FunctionSymbol)this.fSymb).getArity() == 0;
        }
    }

    /**
     * Returns the outer FunctionSymbol or null if this term is a Variable
     */
    public FunctionSymbol getSymbol() {
        return this.fSymb;
    }

    public ACnCTerm apply(ExtVarAbstraction sub) {
        ACnCTerm res;
        Collection<ACnCTerm> e = null;
        ArrayList<ACnCTerm> args = new ArrayList<ACnCTerm>();
        if(this.hasArgs) {
            e = this.args;
        }
        else if(this.hasMultiargs) {
            e = this.multiargs.elements();
        }

        if(e!=null) {
            for (ACnCTerm cand : e) {
                TRSVariable var = sub.get(cand);
                if(var!=null) {
                    ACnCTerm vart = ACnCTerm.create(var, this.acFs, this.cFs);
                    if(this.hasArgs) {
                        args.add(vart);
                    }
                    else {
                        for(int i=0;i<this.multiargs.numberOfOccurences(cand);i++) {
                            args.add(vart);
                        }
                    }
                }
                else {
                    if(this.hasArgs) {
                        args.add(cand);
                    }
                    else {
                        for(int i=0;i<this.multiargs.numberOfOccurences(cand);i++) {
                            args.add(cand);
                        }
                    }
                }
            }
            if(this.hasArgs) {
                res = ACnCTerm.create(this.fSymb, args, this.acFs, this.cFs);
            }
            else {
                res = ACnCTerm.create(this.fSymb, MultisetOfACnCTerms.create(args), this.acFs, this.cFs);
            }
        }
        else {
            res = this.deepcopy();
        }

        return res;
    }

    /** Returns the length of this AC and C-term.
     */
    public int length() {
        int res = 1;
        if(this.isVariable() || this.isConstant()) {
            return res;
        }
        if(this.hasArgs) {
            for(ACnCTerm e : this.args) {
                res += e.length();
            }
        }
        else {
            for(ACnCTerm t : this.multiargs.toRealTermArrayList()) {
                res += t.length();
            }
        }
        return res;
    }

    /** Returns the alien subterms, e.g. arguments of subterms which are ACnCTerms in the Theory of this.acFs.
     */
    public Set<ACnCTerm> getAliens() {
        Set<ACnCTerm> res = new HashSet<ACnCTerm>();

        if(this.hasArgs) {
            /* free symbol */
            for(ACnCTerm t : this.args) {
                res.addAll(this.collectAliens(t));
            }
        }
        else if(this.hasMultiargs) {
            /* AC or C, i.e. get all immediate aliens */
            for(ACnCTerm t : this.multiargs.toTermArrayList()) {
                if(!t.isVariable() && !t.isConstant()) {
                    /* it's an alien! */
                    res.add(t);
                }
            }
        }

        return res;
    }

    /**
     * Helper function for function getAliens()
     */
    private Set<ACnCTerm> collectAliens(ACnCTerm t) {
        Set<ACnCTerm> res = new HashSet<ACnCTerm>();

        if(!t.isVariable() && !t.isConstant()) {
            if(this.acFs.contains(t.getSymbol()) || this.cFs.contains(t.getSymbol())) {
                /* alien! */
                res.add(t);
            }
            else {
                /* descend into subterms */
                if(t.hasArgs) {
                    for(ACnCTerm st : t.args) {
                        res.addAll(this.collectAliens(st));
                    }
                }
                else if(t.hasMultiargs) {
                    for(ACnCTerm st : t.multiargs.toTermArrayList()) {
                        res.addAll(this.collectAliens(st));
                    }
                }
            }
        }

        return res;
    }

    /** Returns the set of variables that are immediate arguments of this AC and C-term and occur exactly once in the
     * AC-term, if this is a Variable the set of this.term is returned.
     */
    public Set<TRSVariable> getLinearImmediateVars() {
        Set<TRSVariable> res = new HashSet<TRSVariable>();
        if(this.isVariable()) {
            res.add((TRSVariable) this.term);
        }
        if(this.isVariable() || this.isConstant()) {
            return res;
        }

        if(this.hasArgs) {
            for(ACnCTerm arg : this.args) {
                if(arg.isVariable() && this.term.getVariableCount().get((TRSVariable)arg.term)==1) {
                    res.add((TRSVariable)arg.term);
                }
            }
        }
        else if(this.hasMultiargs) {
            for(ACnCTerm arg : this.multiargs.toTermArrayList()) {
                if(arg.isVariable() && this.term.getVariableCount().get((TRSVariable)arg.term)==1) {
                    res.add((TRSVariable)arg.term);
                }
            }
        }
        return res;
    }


    /** Returns a multiset of the variables occuring in this AC-term.
     */
    public MultisetOfACnCTerms getVars() {
        ArrayList<ACnCTerm> res = new ArrayList<ACnCTerm>();

        if(this.isVariable()) {
            res.add(this);
        }
        if(this.isVariable() || this.isConstant()) {
            return MultisetOfACnCTerms.create(res);
        }

        if(this.hasArgs) {
            for(ACnCTerm arg : this.args) {
                res.addAll(arg.getVars().toRealTermArrayList());
            }
        }
        else {
            for(ACnCTerm arg : this.multiargs.toRealTermArrayList()) {
                res.addAll(arg.getVars().toRealTermArrayList());
            }
        }

        return MultisetOfACnCTerms.create(res);
    }

    public Collection<ACnCTerm> elements() {
        if(this.hasArgs) {
            return this.args;
        }
        else if(this.hasMultiargs) {
            return this.multiargs.elements();
        }
        else {
            return null;
        }
    }

    public boolean hasArgs() {
        return this.hasArgs;
    }

    public List<ACnCTerm> getArgs() {
        return this.args;
    }

    public boolean hasMultiArgs() {
        return this.hasMultiargs;
    }

    public MultisetOfACnCTerms getMultiargs() {
        return this.multiargs;
    }

    public List<ACnCTerm> getArgVec() {
        List<ACnCTerm> res;
        if(this.hasArgs) {
            res = new ArrayList<ACnCTerm>(this.args);
        } else {
            res = new ArrayList<ACnCTerm>();
            if(this.hasMultiargs) {

                for (ACnCTerm t : this.multiargs.elements()) {
                    int n = this.multiargs.numberOfOccurences(t);
                    for(int i=0; i<n; i++) {
                        res.add(t);
                    }
                }
            }
        }
        return res;
    }

    /**
     * Two ACnCTerms are equal iff they are both Variables,
     * they are the same FunctionSymbol with arity 0,
     * or if they have the same FuntionSymbol and (either have
     * both multiargs which are the same or otherwise have both
     * args which are the same).
     */
    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o instanceof ACnCTerm) {
            ACnCTerm other = (ACnCTerm)o;
            if(this.term.isVariable() || other.term.isVariable()) {
                return this.term.equals(other.term);
            }
            boolean res = this.fSymb.equals(other.fSymb);
            if(res && (this.fSymb.getArity()==0) ) {
                return res;
            }
            if(res) {
                if(this.hasMultiargs && other.hasMultiargs) {
                    res = this.multiargs.equals(other.multiargs);
                }
                else if(this.hasArgs && other.hasArgs) {
                    Iterator i1;
                    Iterator i2;
                    i1 = this.args.iterator();
                    i2 = other.args.iterator();
                    ACnCTerm s;
                    ACnCTerm t;
                    while(i1.hasNext() && res==true) {
                        s = (ACnCTerm)i1.next();
                        t = (ACnCTerm)i2.next();
                        res = s.equals(t);
                    }
                }
                else if(this.hasArgs || this.hasMultiargs) {
                    /* one term has multiargs, the other one args */
                    res = false;
                }
            }
            return res;
        }
        return false;
    }

    /** Returns a string representation of this multiset.
     */
    @Override
    public String toString() {
        StringBuffer res = new StringBuffer();
        if(this.fSymb != null) {
            res.append(this.fSymb.getName());
        }
        else {
            return this.term.toString();
        }

        ArrayList<String> argStrings = null;
        if(this.multiargs != null) {
            argStrings = new ArrayList<String>();
            for(ACnCTerm t : this.multiargs.toRealTermArrayList()) {
                argStrings.add(t.toString());
            }
        }
        if(this.args != null) {
            argStrings = new ArrayList<String>();
            for(ACnCTerm t : this.args) {
                argStrings.add(t.toString());
            }
        }
        if(!this.isConstant() && argStrings != null) {
            res.append("(");
            Iterator i = argStrings.iterator();
            while(i.hasNext()) {
                res.append(i.next().toString());
                if(i.hasNext()) {
                    res.append(", ");
                }
            }
            res.append(")");
        }

        return res.toString();
    }

    /** Returns a term representation of this multiterm.
     */
    public TRSTerm toTerm() {
        return this.term;
    }

    /** Returns a deep copy of this multiterm.
     */
    public ACnCTerm deepcopy() {
        return new ACnCTerm(this.toTerm(), this.acFs, this.cFs);
    }

    private String toHashString() {
        StringBuffer res = new StringBuffer();
        if(this.fSymb != null) {
            res.append(this.fSymb.getName());
        }
        else {
            return this.term.toString();
        }
        if(!this.isConstant()) {
            if(this.multiargs != null) {
                res.append(this.multiargs.toString());
            }
            if(this.args != null) {
                res = res.append(this.args.toString());
            }
        }
        return res.toString();
    }

    @Override
    public int hashCode() {
        return this.toHashString().hashCode();
    }

    public ACTerm toACTerm() {
        return ACTerm.create(this.term, this.acFs);
    }

}

