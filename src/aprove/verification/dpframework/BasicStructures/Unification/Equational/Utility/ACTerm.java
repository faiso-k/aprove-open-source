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
 * An ACTerm is a term representation where the AC arguments are flattened
 * and put into a multiset, so nested AC symbols will be dropped and the
 * AC Symbols will have variable arity.
 * Needed for AC unification.
 *
 * @author Stephan Falke
 * @version $Id$
 */


public class ACTerm implements Immutable{

    private TRSTerm term; // term representation of this ACTerm
    private MultisetOfACTerms multiargs; //args represented as a multiset, if fSymb is AC
    private boolean hasMultiargs;
    private ImmutableArrayList<ACTerm> args;
    private boolean hasArgs;
    private FunctionSymbol fSymb; //the outer FunctionSymbol or null if this term is a Variable
    private ImmutableArrayList<FunctionSymbol> acFs; //FunctionSymbols that are AC


    private ACTerm(FunctionSymbol f, ArrayList<ACTerm> args, Collection<FunctionSymbol> acFs) {
        this.multiargs = null;
        this.args = ImmutableCreator.create(args);
        this.hasArgs = true;
        this.hasMultiargs = false;

        this.acFs = ImmutableCreator.create(new ArrayList<FunctionSymbol>(acFs));
        this.fSymb = f;
        this.term = this.constructTerm();
    }

    private ACTerm(FunctionSymbol f, MultisetOfACTerms multiargs, Collection<FunctionSymbol> acFs) {
        this.multiargs = multiargs;
        this.args = null;
        this.hasArgs = false;
        this.hasMultiargs = true;

        this.acFs = ImmutableCreator.create(new ArrayList<FunctionSymbol>(acFs));
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
            for(ACTerm i : this.args) {
                newArgs.add(i.toTerm());
            }
            return TRSTerm.createFunctionApplication(this.fSymb, ImmutableCreator.create(newArgs));
        }
        else {
            ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>();
            for(ACTerm s : this.multiargs.toTermArrayList()) {
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

    private ACTerm(TRSTerm t, Collection<FunctionSymbol> AcFs) {
        this.multiargs = null;
        this.args = null;
        this.hasArgs = false;
        this.hasMultiargs = false;

        this.term = t;
        this.acFs = ImmutableCreator.create(new ArrayList<FunctionSymbol>(AcFs));

        if(t.isVariable()) {
            return;
        }
        else {
            this.fSymb = ((TRSFunctionApplication)t).getRootSymbol();
            if(AcFs.contains(this.fSymb)) {
                this.hasMultiargs = true;
                ArrayList<ACTerm> multiVec = new ArrayList<ACTerm>();
                for(TRSTerm i : ((TRSFunctionApplication)t).getArguments()) {
                    ACTerm s = ACTerm.create(i, AcFs);
                    if(!(i instanceof TRSVariable) && s.fSymb.equals(this.fSymb)) {
                        multiVec.addAll(s.multiargs.toRealTermArrayList());
                    }
                    else {
                        multiVec.add(s);
                    }
                }
                this.multiargs = MultisetOfACTerms.create(multiVec);
            }
            else {
                this.hasArgs = true;
                ArrayList<ACTerm> args = new ArrayList<ACTerm>();
                for(TRSTerm i : ((TRSFunctionApplication)t).getArguments()) {
                    args.add(ACTerm.create(i, AcFs));
                }
                this.args = ImmutableCreator.create(args);
            }
        }
    }

    /** Returns a new instance of <code>ACTerm</code>.
     * @param t   the term that's to be transformed into an ACTerm
     * @param Fac   the AC symbols
     */
    public static ACTerm create(TRSTerm t, Collection<FunctionSymbol> Fac) {
        return new ACTerm(t, Fac);
    }

    /** Returns a new instance of <code>ACTerm</code>.
     * @param f     the head function symbol
     * @param args  the arguments
     * @param Fac   the AC symbols
     */
    public static ACTerm create(FunctionSymbol f, ArrayList<ACTerm> args, Collection<FunctionSymbol> Fac) {
        return new ACTerm(f, args, Fac);
    }

    /** Returns a new instance of <code>ACTerm</code>.
     * @param f     the head function symbol
     * @param multiargs  the arguments
     * @param Fac   the AC symbols
     */
    public static ACTerm create(FunctionSymbol f, MultisetOfACTerms multiargs, Collection<FunctionSymbol> Fac) {
        return new ACTerm(f, multiargs, Fac);
    }

    public Collection<FunctionSymbol> getAcFs() {
        return this.acFs;
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

    public ACTerm apply(VarAbstraction sub) {
        ACTerm res;
        Collection<ACTerm> e = null;
        ArrayList<ACTerm> args = new ArrayList<ACTerm>();
        if(this.hasArgs) {
            e = this.args;
        }
        else if(this.hasMultiargs) {
            e = this.multiargs.elements();
        }

        if(e!=null) {
            for (ACTerm cand : e) {
                TRSVariable var = sub.get(cand);
                if(var!=null) {
                    ACTerm vart = ACTerm.create(var, this.acFs);
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
                res = ACTerm.create(this.fSymb, args, this.acFs);
            }
            else {
                res = ACTerm.create(this.fSymb, MultisetOfACTerms.create(args), this.acFs);
            }
        }
        else {
            res = this.deepcopy();
        }

        return res;
    }

    /** Returns the length of this AC-term.
     */
    public int length() {
        int res = 1;
        if(this.isVariable() || this.isConstant()) {
            return res;
        }
        if(this.hasArgs) {
            for(ACTerm e : this.args) {
                res += e.length();
            }
        }
        else {
            for(ACTerm t : this.multiargs.toRealTermArrayList()) {
                res += t.length();
            }
        }
        return res;
    }

    /** Returns the alien subterms, e.g. arguments of subterms which are ACTerms in the Theory of this.acFs.
     */
    public Set<ACTerm> getAliens() {
        Set<ACTerm> res = new HashSet<ACTerm>();

        if(this.hasArgs) {
            /* free symbol */
            for(ACTerm t : this.args) {
                res.addAll(this.collectAliens(t));
            }
        }
        else if(this.hasMultiargs) {
            /* AC, i.e. get all immediate aliens */
            for(ACTerm t : this.multiargs.toTermArrayList()) {
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
    private Set<ACTerm> collectAliens(ACTerm t) {
        Set<ACTerm> res = new HashSet<ACTerm>();

        if(!t.isVariable() && !t.isConstant()) {
            if(this.acFs.contains(t.getSymbol())) {
                /* alien! */
                res.add(t);
            }
            else {
                /* descend into subterms */
                if(t.hasArgs) {
                    for(ACTerm st : t.args) {
                        res.addAll(this.collectAliens(st));
                    }
                }
                else if(t.hasMultiargs) {
                    for(ACTerm st : t.multiargs.toTermArrayList()) {
                        res.addAll(this.collectAliens(st));
                    }
                }
            }
        }

        return res;
    }

    /** Returns the set of variables that are immediate arguments of this AC-term and occur exactly once in the
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
            for(ACTerm arg : this.args) {
                if(arg.isVariable() && this.term.getVariableCount().get((TRSVariable)arg.term)==1) {
                    res.add((TRSVariable)arg.term);
                }
            }
        }
        else if(this.hasMultiargs) {
            for(ACTerm arg : this.multiargs.toTermArrayList()) {
                if(arg.isVariable() && this.term.getVariableCount().get((TRSVariable)arg.term)==1) {
                    res.add((TRSVariable)arg.term);
                }
            }
        }
        return res;
    }


    /** Returns a multiset of the variables occuring in this AC-term.
     */
    public MultisetOfACTerms getVars() {
        ArrayList<ACTerm> res = new ArrayList<ACTerm>();

        if(this.isVariable()) {
            res.add(this);
        }
        if(this.isVariable() || this.isConstant()) {
            return MultisetOfACTerms.create(res);
        }

        if(this.hasArgs) {
            for(ACTerm arg : this.args) {
                res.addAll(arg.getVars().toRealTermArrayList());
            }
        }
        else {
            for(ACTerm arg : this.multiargs.toRealTermArrayList()) {
                res.addAll(arg.getVars().toRealTermArrayList());
            }
        }

        return MultisetOfACTerms.create(res);
    }

    public Collection<ACTerm> elements() {
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

    public List<ACTerm> getArgs() {
        return this.args;
    }

    public boolean hasMultiArgs() {
        return this.hasMultiargs;
    }

    public MultisetOfACTerms getMultiargs() {
        return this.multiargs;
    }

    /**
     * Two ACTerms are equal iff they are both Variables,
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
        if (o instanceof ACTerm) {
            ACTerm other = (ACTerm)o;
            if(this.term.isVariable() || other.term.isVariable()) {
                return this.term.equals(other.term);
            }
            boolean res = this.fSymb.equals(other.fSymb);
            if(res && (((FunctionSymbol)this.fSymb).getArity()==0) ) {
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
                    ACTerm s;
                    ACTerm t;
                    while(i1.hasNext() && res==true) {
                        s = (ACTerm)i1.next();
                        t = (ACTerm)i2.next();
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
            for(ACTerm t : this.multiargs.toRealTermArrayList()) {
                argStrings.add(t.toString());
            }
        }
        if(this.args != null) {
            argStrings = new ArrayList<String>();
            for(ACTerm t : this.args) {
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
    public ACTerm deepcopy() {
        return new ACTerm(this.toTerm(), this.acFs);
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

    public ACnCTerm toACnCTerm(Set<FunctionSymbol> cs) {
        return ACnCTerm.create(this.term, this.acFs, cs);
    }

}

