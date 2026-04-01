/*
 * Created on 11.04.2005
 */
package aprove.verification.dpframework.BasicStructures;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.runtime.*;
import aprove.verification.dpframework.BasicStructures.Unification.Equational.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * A FunctionApplication is a term that consists of a function symbol f/n and a list of arguments of size n. Two
 * FunctionApplications are equal iff their root-symbol is equal and their arguments are equal.
 * @author thiemann
 */
public abstract class TRSFunctionApplication extends TRSTerm implements FunctionExpression {

    /**
     * These static fields need to be initialized lazily, because otherwise a cyclic dependency in the class loading causes a NullPointerException.
     */
    private static FunctionSymbol UNARY_MINUS;;
    private static FunctionSymbol BINARY_MINUS;
    private static FunctionSymbol BINARY_PLUS;
    private static FunctionSymbol BINARY_MULT;

    private static FunctionSymbol getUnaryMinus() {
        if (UNARY_MINUS == null) {
            UNARY_MINUS = IDPPredefinedMap.DEFAULT_MAP.getSym(Func.UnaryMinus, DomainFactory.INTEGERS);
        }
        return UNARY_MINUS;
    }

    private static FunctionSymbol getBinaryMinus() {
        if (BINARY_MINUS == null) {
            BINARY_MINUS = IDPPredefinedMap.DEFAULT_MAP.getSym(Func.Sub, DomainFactory.INTEGER_INTEGER);
        }
        return BINARY_MINUS;
    }

    private static FunctionSymbol getBinaryPlus() {
        if (BINARY_PLUS == null) {
            BINARY_PLUS = IDPPredefinedMap.DEFAULT_MAP.getSym(Func.Add, DomainFactory.INTEGER_INTEGER);
        }
        return BINARY_PLUS;
    }

    private static FunctionSymbol getBinaryMult() {
        if (BINARY_MULT == null) {
            BINARY_MULT = IDPPredefinedMap.DEFAULT_MAP.getSym(Func.Mul, DomainFactory.INTEGER_INTEGER);
        }
        return BINARY_MULT;
    }
    
    /**
     * @param term Some function application.
     * @param Q
     * @param lhsR A mapping from functionSymbols to lhss of rules with corresponding root symbol.
     * @param s
     * @param startNr The start number for introducing fresh variables.
     * @return The result of icapQRs(term).
     */
    protected static ImmutablePair<TRSTerm, Integer> icapQRst(
        TRSFunctionApplication term,
        QTermSet Q,
        Map<FunctionSymbol, Set<TRSFunctionApplication>> lhsR,
        TRSFunctionApplication s,
        Integer startNr
    ) {
        Integer nr = startNr;
        final ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>(term.getRootSymbol().getArity());
        for (TRSTerm arg : term.getArguments()) {
            final ImmutablePair<TRSTerm, Integer> newArgInt = arg.icapQRst(Q, lhsR, s, nr);
            nr = newArgInt.y;
            newArgs.add(newArgInt.x);
        }
        TRSTerm newTerm;
        if (nr == startNr) { // no equals necessary by construction of code
            // if the numbers are equal we did not change anything, hence
            // we do not need a new object!
            newTerm = term;
        } else {
            newTerm = TRSTerm.createFunctionApplication(term.getRootSymbol(), newArgs);
        }
        final Set<TRSFunctionApplication> possibleLhs = lhsR.get(term.getRootSymbol());
        if (possibleLhs != null) {
            for (TRSFunctionApplication lhs : possibleLhs) {
                final TRSSubstitution delta = lhs.getMGU(newTerm);
                if (delta != null) {
                    if (Q.canBeRewritten(s.applySubstitution(delta))) {
                        // s delta not Q normal
                        // do not cap
                    } else {
                        boolean li_sigma_not_Q_normal = false;
                        for (TRSTerm lhsArg : lhs.getArguments()) {
                            if (Q.canBeRewritten(lhsArg.applySubstitution(delta))) {
                                li_sigma_not_Q_normal = true;
                                break;
                            }
                        }
                        if (li_sigma_not_Q_normal) {
                            // some li sigma is not Q normal
                            // do not cap
                        } else {
                            // s delta is Q normal
                            // all li delta are Q normal
                            // => we must cap
                            newTerm = new TRSVariable(TRSTerm.SECOND_STANDARD_PREFIX + nr);
                            nr++;
                            break;
                        }
                    }
                }
            }
        }
        return new ImmutablePair<TRSTerm, Integer>(newTerm, nr);
    }

    /**
     * @param term Some function application.
     * @param lhsR
     * @param startNr
     * @return The result of tcapR(term).
     */
    protected static ImmutablePair<TRSTerm, Integer> tcap(
        TRSFunctionApplication term,
        Map<FunctionSymbol, Set<TRSFunctionApplication>> lhsR,
        Integer startNr
    ) {
        Integer nr = startNr;
        final ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>(term.getArguments().size());
        for (TRSTerm arg : term.getArguments()) {
            final ImmutablePair<TRSTerm, Integer> argRes = arg.tcap(lhsR, nr);
            nr = argRes.y;
            newArgs.add(argRes.x);
        }
        TRSTerm newTerm;
        if (nr == startNr) { // no equals necessary by construction of code
            // if the numbers are equal we did not change anything, hence
            // we do not need a new object!
            newTerm = term;
        } else {
            newTerm = TRSTerm.createFunctionApplication(term.getRootSymbol(), newArgs);
        }
        final Set<TRSFunctionApplication> possLhss = lhsR.get(term.getRootSymbol());
        if (possLhss != null) {
            for (TRSFunctionApplication lhs : possLhss) {
                if (lhs.unifies(newTerm)) {
                    newTerm = new TRSVariable(TRSTerm.SECOND_STANDARD_PREFIX + nr);
                    nr++;
                    break;
                }
            }
        }
        return new ImmutablePair<TRSTerm, Integer>(newTerm, nr);
    }

    /**
     * @param term Some function application.
     * @param lhsR
     * @param ACs
     * @param Cs
     * @param startNr
     * @return The result of tcapE(term).
     */
    protected static ImmutablePair<TRSTerm, Integer> tcapE(
        TRSFunctionApplication term,
        Map<FunctionSymbol, Set<TRSFunctionApplication>> lhsR,
        Set<FunctionSymbol> ACs,
        Set<FunctionSymbol> Cs,
        Integer startNr
    ) {
        Integer nr = startNr;
        final ArrayList<TRSTerm> newArgs = new ArrayList<>(term.getArguments().size());
        for (TRSTerm arg : term.getArguments()) {
            final ImmutablePair<TRSTerm, Integer> argRes = arg.tcapE(lhsR, ACs, Cs, nr);
            nr = argRes.y;
            newArgs.add(argRes.x);
        }
        TRSTerm newTerm;
        FunctionSymbol f = term.getRootSymbol();
        if (nr == startNr) { // no equals necessary by construction of code
            // if the numbers are equal we did not change anything, hence
            // we do not need a new object!
            newTerm = term;
        } else {
            newTerm = TRSTerm.createFunctionApplication(f, newArgs);
        }
        if (Options.certifier.isCeta() && (ACs.contains(f) || Cs.contains(f))) {
            newTerm = new TRSVariable(TRSTerm.SECOND_STANDARD_PREFIX + nr);
            nr++;
            return new ImmutablePair<>(newTerm, nr);
        }
        final Set<TRSFunctionApplication> possLhss = lhsR.get(f);
        if (possLhss != null) {
            for (TRSFunctionApplication lhs : possLhss) {
                if ((!Cs.isEmpty() && new GeneralACnC(ACs, Cs).areTheoryUnifiable(lhs, newTerm))
                    || (Cs.isEmpty() && new GeneralAC(ACs).areTheoryUnifiable(lhs, newTerm))) {
                    newTerm = new TRSVariable(TRSTerm.SECOND_STANDARD_PREFIX + nr);
                    nr++;
                    break;
                }
            }
        }
        return new ImmutablePair<>(newTerm, nr);
    }

    /**
     * A method for checking whether the arguments for the constructors are okay. Used for assertions.
     * @param f Some function symbol.
     * @param args Some arguments.
     * @return True if both the function symbol and all arguments are non-null and the arity of the function symbols is
     *         equal to the number of arguments.
     */
    private static boolean checkValidConstructorArgs(FunctionSymbol f, List<? extends TRSTerm> args) {
        if (f != null && args != null && f.getArity() == args.size()) {
            for (TRSTerm arg : args) {
                if (arg == null) {
                    return false;
                }
            }
            return true;
        } else {
            return false;
        }
    }

    /**
     * Arguments.
     */
    private final ImmutableList<? extends TRSTerm> args;

    /**
     * Function symbol.
     */
    private final FunctionSymbol f;

    public FunctionSymbol getFunctionSymbol() {
        return f;
    }
    
    /**
     * Cached hash value.
     */
    private final int hashCode;

    /**
     * @param f - a non null function symbol of arity n
     * @param args - a vector of length n where all terms are non-null
     */
    protected TRSFunctionApplication(FunctionSymbol f, ImmutableList<? extends TRSTerm> args) {
        if (Globals.useAssertions) {
            assert (TRSFunctionApplication.checkValidConstructorArgs(f, args));
        }
        this.f = f;
        this.args = args;
        int hash = f.hashCode() * 93201;
        for (TRSTerm arg : args) {
            hash += arg.hashCode() * 323289;
        }
        this.hashCode = hash;
    }

    @Override
    public abstract TRSFunctionApplication applySubstitution(Substitution sigma);

    @Override
    public void collectFunctionSymbols(Set<FunctionSymbol> fs) {
        fs.add(this.f);
        for (TRSTerm arg : this.args) {
            arg.collectFunctionSymbols(fs);
        }
    }

    @Override
    public void collectVariables(Set<TRSVariable> vars) {
        for (TRSTerm arg : this.args) {
            arg.collectVariables(vars);
        }
    }

    @Override
    public int compareTo(TRSTerm t) {
        if (t.isVariable()) {
            return 1;
        } else {
            final TRSFunctionApplication gt = (TRSFunctionApplication)t;
            int compare = gt.f.compareTo(this.f);
            if (compare == 0) {
                int i = 0;
                final List<? extends TRSTerm> otherArgs = gt.args;
                for (TRSTerm thisArg : this.args) {
                    compare = thisArg.compareTo(otherArgs.get(i));
                    if (compare == 0) {
                        i++;
                    } else {
                        return compare;
                    }
                }
                return 0;
            } else {
                return compare;
            }
        }
    }

    @Override
    public void computeFunctionSymbolCount(Map<FunctionSymbol, Integer> map) {
        final Integer old = map.put(this.f, 1);
        if (old != null) {
            map.put(this.f, old + 1);
        }
        for (TRSTerm arg : this.args) {
            arg.computeFunctionSymbolCount(map);
        }
    }

    @Override
    public void computeVariableCount(Map<TRSVariable, Integer> map) {
        for (TRSTerm arg : this.args) {
            arg.computeVariableCount(map);
        }
    }

    @Override
    public boolean equals(Object other) {
        if (this == other) {
            return true;
        }
        if (other instanceof TRSFunctionApplication) {
            final TRSFunctionApplication t = (TRSFunctionApplication)other;
            return this.hashCode == t.hashCode && this.f.equals(t.f) && this.args.equals(t.args);
        }
        return false;
    }

    @Override
    public String export(Export_Util eu) {
        return this.export(eu, java.util.Collections.<TRSVariable>emptySet());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String export(Export_Util eu,
        java.util.Collection<TRSVariable> freeVars) {
        final StringBuilder temp = new StringBuilder();
        temp.append(this.f.export(eu));
        final Iterator<? extends TRSTerm> i = this.args.iterator();
        if (i.hasNext()) {
            temp.append("(");
            final TRSTerm arg = i.next();
            temp.append(arg.export(eu, freeVars));
            while (i.hasNext()) {
                temp.append(", ");
                temp.append(i.next().export(eu, freeVars));
            }
            temp.append(")");
        }
        return temp.toString();
    }

    @Override
    public Map<TRSVariable, TRSTerm> extendMatchingSubstitution(Map<TRSVariable, TRSTerm> sigmaParam, TRSTerm that) {
        Map<TRSVariable, TRSTerm> sigma = sigmaParam;
        if (that instanceof TRSVariable) {
            return null;
        }
        final TRSFunctionApplication fThat = (TRSFunctionApplication)that;
        if (this.f.equals(fThat.f)) {
            final int n = this.f.getArity();
            for (int i = 0; i < n; i++) {
                sigma = this.args.get(i).extendMatchingSubstitution(sigma, fThat.args.get(i));
                if (sigma == null) {
                    return null;
                }
            }
            return sigma;
        } else {
            return null;
        }
    }

    /**
     * @param index Some index.
     * @return The index'th argument of this term (constant time).
     */
    public TRSTerm getArgument(int index) {
        return this.args.get(index);
    }

    /**
     * @return The arguments of this Term as immutable list (constant time).
     */
    @SuppressWarnings("unchecked")
    public ImmutableList<TRSTerm> getArguments() {
        /*
         * Casting ImmutableArrayList<? extends Term> to ImmutableArrayList<Term>
         * is ok here, as the list is immutable, so it can not be compromised
         * by e.g. adding FunctionApplications to a ImmutableArrayList<Variable>.
         */
        return (ImmutableList<TRSTerm>)this.args;
    }

    @Override
    public int getDepth() {
        int currentMaximum = 0;
        for (TRSTerm arg : this.args) {
            final int currentDepth = arg.getDepth() + 1;
            if (currentDepth > currentMaximum) {
                currentMaximum = currentDepth;
            }
        }
        return currentMaximum;
    }

    @Override
    public int getDepthConstant() {
        int currentMaximum = 0;
        for (TRSTerm arg : this.args) {
            final int currentDepth = arg.getDepthConstant();
            if (currentDepth > currentMaximum) {
                currentMaximum = currentDepth;
            }
        }
        return currentMaximum + 1;
    }

    /**
     * @return A set of all function symbols occurring at a non-root position in this term.
     */
    public Set<FunctionSymbol> getNonRootFunctionSymbols() {
        final Set<FunctionSymbol> fs = new LinkedHashSet<FunctionSymbol>();
        for (TRSTerm arg : this.args) {
            arg.collectFunctionSymbols(fs);
        }
        return fs;
    }

    @Override
    public FunctionSymbol getRootSymbol() {
        return this.f;
    }

    @Override
    public int getSize() {
        int size = 1;
        for (TRSTerm arg : this.args) {
            size += arg.getSize();
        }
        return size;
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

    @Override
    public boolean isConstant() {
        return this.f.getArity() == 0;
    }

    /**
     * @author Sebastian Weise
     */
    @Override
    public boolean isGroundTerm() {
        for (TRSTerm actSubTerm : this.args) {
            if (!actSubTerm.isGroundTerm()) {
                return false;
            }
        }
        return true;
    }

    @Override
    public boolean isVariable() {
        return false;
    }

    @Override
    public boolean linearMatches(TRSTerm that) {
        if (that instanceof TRSVariable) {
            return false;
        }
        final TRSFunctionApplication fThat = (TRSFunctionApplication)that;
        if (this.f.equals(fThat.f)) {
            final int n = this.f.getArity();
            for (int i = 0; i < n; i++) {
                if (!this.args.get(i).linearMatches(fThat.args.get(i))) {
                    return false;
                }
            }
            return true;
        } else {
            return false;
        }
    }

    @Override
    public TRSFunctionApplication renameVariables(final Map<TRSVariable, TRSVariable> map) {
        final ArrayList<TRSTerm> newArgs = new ArrayList<>(this.args.size());
        boolean changed = false;
        for (final TRSTerm arg : this.args) {
            TRSTerm resArg = arg.renameVariables(map);
            changed = changed || resArg != arg;
            newArgs.add(resArg);
        }
        final TRSFunctionApplication res = changed ? createFunctionApplication(this.f, ImmutableCreator.create(newArgs)) : this;
        return res;
    }

    @Override
    public abstract TRSFunctionApplication renameVariables(
        aprove.verification.dpframework.BasicStructures.Utility.FreshVarGenerator gen
    );

    @Override
    public abstract ImmutablePair<? extends TRSFunctionApplication, Integer> renumberVariables(
        Map<TRSVariable, TRSVariable> map,
        String prefix,
        Integer nrParam
    );

    /**
     * @param replace The function symbol to be replaced.
     * @param replacement The new function symbol. Must have the same arity as replace.
     * @return A new TRSFunctionApplication where all occurrences of the specified function symbol replace are replaced
     *         by the function symbol replacement.
     */
    public abstract TRSFunctionApplication replaceAll(FunctionSymbol replace, FunctionSymbol replacement);

    public TRSFunctionApplication renameAt(Position pos, FunctionSymbol replacement) {
        final TRSTerm _subterm = this.getSubterm(pos);
        if (_subterm.isVariable()) {return this;}  // TODO: copy?
        final TRSFunctionApplication subterm = (TRSFunctionApplication) _subterm;
        final TRSFunctionApplication subterm_new = createFunctionApplication(replacement, subterm.getArguments());
        return (TRSFunctionApplication) this.replaceAt(pos, subterm_new);
    }

    public TRSFunctionApplication renameAtMap(Position pos, Map<FunctionSymbol, FunctionSymbol> replacements) {
        final TRSTerm _subterm = this.getSubterm(pos);
        if (_subterm.isVariable()) {return this;}
        final TRSFunctionApplication subterm = (TRSFunctionApplication) _subterm;
        final FunctionSymbol root = subterm.getRootSymbol();
        final FunctionSymbol root_new = replacements.getOrDefault(root, root);
        final TRSFunctionApplication subterm_new = createFunctionApplication(root_new, subterm.getArguments());
        return (TRSFunctionApplication) this.replaceAt(pos, subterm_new);
    }

    public TRSFunctionApplication renameAtAllMap(Set<Position> poses, Map<FunctionSymbol, FunctionSymbol> replacements) {
        TRSFunctionApplication res = this;
        for (Position pos: poses) {
            res = (TRSFunctionApplication) res.renameAtMap(pos, replacements);
        }
        return res;
    }

    /**
     * Applies tcap only on non-epsilon positions. All fresh variables will be disjoint. We have the same requirements
     * as for tcap.
     * @param lhsR TODO
     * @return TODO
     */
    public abstract TRSFunctionApplication tcapNe(Map<FunctionSymbol, Set<TRSFunctionApplication>> lhsR);

    @Override
    public Element toCPF2(Document doc, XMLMetaData xmlMetaData) {
        final Element e = CPFTag.FUNAPP.createElement(doc);
        e.appendChild(this.f.toCPF(doc, xmlMetaData));
        CollectionUtils.addCPFChildren(this.args, e, doc, xmlMetaData);
        return e;
    }

    @Override
    public Element toDOM2(Document doc, XMLMetaData xmlMetaData) {
        final Element e = XMLTag.FUNCTION_APPLICATION.createElement(doc);
        e.appendChild(this.f.toDOM(doc, xmlMetaData));
        CollectionUtils.addChildren(this.args, e, doc, xmlMetaData);
        return e;
    }

    @Override
    public String toJSON() {
        return this.toSExpressionString();
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public String toTERMPTATION(FreshNameGenerator vars, FreshNameGenerator funcs) {
        final ImmutableList<? extends TRSTerm> argsVar = this.getArguments();
        final FunctionSymbol fsym = this.getRootSymbol();
        final StringBuffer res = new StringBuffer(funcs.getFreshName(fsym.getName(), true));
        if (fsym.getArity() > 0) {
            res.append("(");
            final Iterator<?> i = argsVar.iterator();
            while (i.hasNext()) {
                // apply this visitor to arguments
                final TRSTerm t = (TRSTerm)i.next();
                final String temp = t.toTERMPTATION(vars, funcs);
                res.append(temp);
                if (i.hasNext()) {
                    res.append(", ");
                }
            }
            res.append(")");
        }
        return res.toString();
    }

    @Override
    protected void collectLeafPositions(Position pos, Collection<Position> pts) {
        if (this.f.getArity() == 0) { // we're a leaf!
            pts.add(pos);
        } else { // the leaves are below
            int i = 0;
            for (TRSTerm arg : this.args) {
                final Position posArg = pos.append(i);
                arg.collectLeafPositions(posArg, pts);
                i++;
            }
        }
    }

    @Override
    protected void collectPositions(Position pos, Collection<Position> pts) {
        pts.add(pos);
        int i = 0;
        for (TRSTerm arg : this.args) {
            final Position posArg = pos.append(i);
            arg.collectPositions(posArg, pts);
            i++;
        }
    }

    @Override
    protected void collectPositionsAndSubTerms(
        Position pos,
        Collection<Pair<Position, TRSTerm>> pts,
        boolean dropRoot,
        boolean dropVars
        ) {
        if (dropRoot) {
            // do not add this position
        } else {
            pts.add(new Pair<Position, TRSTerm>(pos, this));
        }
        int i = 0;
        for (TRSTerm arg : this.args) {
            final Position posArg = pos.append(i);
            arg.collectPositionsAndSubTerms(posArg, pts, false, dropVars);
            i++;
        }
    }
    
    @Override
    protected void collectTree(
    		Position pos,
    		BiTreeNode<Pair<Position, TRSTerm>> parent
    	) {
		BiTreeNode<Pair<Position, TRSTerm>> child;
    	if(parent.getValue() == null) {
    		// we are at root
    		parent.setValue(new Pair<Position, TRSTerm>(pos, this));
    		child = parent;
    	} else {
			child = parent.addChild(new BiTreeNode<Pair<Position, TRSTerm>>(new Pair<Position, TRSTerm>(pos, this)));
    	}
        int i = 0;
        for (TRSTerm arg : this.args) {
            final Position posArg = pos.append(i);;
            arg.collectTree(posArg, child);
            i++;
        }
    }
    

    @Override
    protected void collectSubTerms(Set<TRSTerm> subs, boolean dropVars) {
        if (subs.add(this)) {
            for (TRSTerm arg : this.args) {
                arg.collectSubTerms(subs, dropVars);
            }
        } else {
            // nothing todo
        }
    }

    @Override
    protected void collectVariablePositions(Position pos, Map<TRSVariable, List<Position>> varPositions) {
        int i = 0;
        for (TRSTerm arg : this.args) {
            final Position posArg = pos.append(i);
            arg.collectVariablePositions(posArg, varPositions);
            i++;
        }
    }

    @Override
    protected void computePathLabels(Position pos, int depth, List<FunctionSymbol> fs) {
        final int posDepth = pos.getDepth();
        fs.add(this.f);
        if (depth >= posDepth) {
            return; // no arguments positions to consider any more
        }
        final int argIndex = pos.get(depth);
        if (argIndex >= this.args.size()) {
            return; // the remaining suffix of pos is not in the term
        }
        final TRSTerm arg = this.getArgument(argIndex);
        arg.computePathLabels(pos, depth + 1, fs);
    }

    @Override
    protected boolean isLinear(Set<TRSVariable> alreadyPresent) {
        for (TRSTerm arg : this.args) {
            if (!arg.isLinear(alreadyPresent)) {
                return false;
            }
        }
        return true;
    }

    @Override
    protected boolean testForLessVariables(Map<TRSVariable, Integer> map) {
        for (TRSTerm arg : this.args) {
            if (!arg.testForLessVariables(map)) {
                return false;
            }
        }
        return true;
    }
    
    private static List<TRSTerm> simplify(List<TRSTerm> terms) {
        List<TRSTerm> newTerms = new ArrayList<>(terms.size());
        for (TRSTerm term : terms) {
            newTerms.add(term.simplify());
        }
        return newTerms;
    }
    
    private TRSTerm simplifyUnaryMinus() {
        if (Globals.useAssertions) {
            assert (getFunctionSymbol().equals(getUnaryMinus()));
        }
        TRSTerm arg = getArgument(0);
        if (arg instanceof TRSFunctionApplication) {
            TRSFunctionApplication argFuncAppl = (TRSFunctionApplication)arg;
            FunctionSymbol argFuncSymb = argFuncAppl.getFunctionSymbol();
            // Remove double minus, e.g -(-(x)) becomes x
            if (argFuncSymb.equals(getUnaryMinus())) {
                return argFuncAppl.getArgument(0);
            }
            // Change -(x-y) to y-x
            if (argFuncSymb.equals(getBinaryMinus())) {
                return TRSTerm.createFunctionApplication(getBinaryMinus(), argFuncAppl.getArgument(1), argFuncAppl.getArgument(0));
            }
        }
        if (arg instanceof TRSConstantTerm) {
            Integer constant = Integer.valueOf(((TRSConstantTerm)arg).getValue());
            if (constant != null) {
                return TRSTerm.createConstant(Integer.toString(-constant));
            }
        }
        return this;
    }

    /**
     * Applies all simplification methods assuming this is a binary minus function
     * 
     * These simplifications are:
     * <ul>
     *   <li>Move constants to the back of the term (e.g. (3 - x) to ((-x) - (-3)). Simplified later to (-x + 3)
     *   <li>Resolve constant terms, e.g. (3 - 4) to (-1)
     *   <li>Fold constant of this term with term of subterm, e.g. ((x + 1) - 4) to (x - 3)
     *   <li>Fold constant of this term with term of subterm, e.g. ((x - 1) - 4) to (x - 5)
     *   <li>Simplify (x - (-y)) to (x + y)
     * </ul>
     * 
     * @return A possibly simplified version of this term 
     */
    private TRSTerm simplifyBinaryMinus() {
        // The current function symbol is a binary minus
        if (Globals.useAssertions) {
            assert getFunctionSymbol().equals(getBinaryMinus());
        }

        TRSTerm arg1 = getArgument(0);
        TRSTerm arg2 = getArgument(1);
        
        // Move constant term of minus to the back. Needed for further simplifications
        if (arg1 instanceof TRSConstantTerm && !(arg2 instanceof TRSConstantTerm)) {
            TRSTerm newArg1 = TRSTerm.createFunctionApplication(getUnaryMinus(), arg2);
            TRSTerm newArg2 = TRSTerm.createFunctionApplication(getUnaryMinus(), arg1);
            return TRSTerm.createFunctionApplication(getBinaryMinus(), newArg1, newArg2).simplify();
        }

        if (arg2 instanceof TRSConstantTerm) {
            // Resolve constant terms, e.g. (3 - 4) to (-1)
            if (arg1 instanceof TRSConstantTerm) {
                Integer value1 = Integer.valueOf(((TRSConstantTerm)arg1).getValue());
                Integer value2 = Integer.valueOf(((TRSConstantTerm)arg2).getValue());
                if (value1 != null && value2 != null) {
                    Integer combinedValue = value1 - value2;
                    return TRSTerm.createConstant(combinedValue.toString());
                }
            }
            if (arg1 instanceof TRSFunctionApplication) {
                TRSFunctionApplication arg1FuncAppl = (TRSFunctionApplication)arg1;
                FunctionSymbol arg1FuncSymb = arg1FuncAppl.getFunctionSymbol();
                // Fold constant of this term with term of subterm, e.g. ((x + 1) - 4) to (x - 3)
                if (arg1FuncSymb.equals(getBinaryPlus())) {
                    TRSTerm arg11 = arg1FuncAppl.getArgument(0);
                    TRSTerm arg12 = arg1FuncAppl.getArgument(1);
                    if (arg12 instanceof TRSConstantTerm) {
                        Integer value1 = Integer.valueOf(((TRSConstantTerm)arg12).getValue());
                        Integer value2 = Integer.valueOf(((TRSConstantTerm)arg2).getValue());
                        if (value1 != null && value2 != null) {
                            Integer combinedValue = value2 - value1;

                            TRSTerm newConstant = TRSTerm.createConstant(combinedValue.toString());
                            return TRSTerm.createFunctionApplication(getBinaryMinus(), arg11, newConstant).simplify();
                        }
                    }
                }
                // Fold constant of this term with term of subterm, e.g. ((x - 1) - 4) to (x - 5)
                if (arg1FuncSymb.equals(getBinaryMinus())) {
                    TRSTerm arg11 = arg1FuncAppl.getArgument(0);
                    TRSTerm arg12 = arg1FuncAppl.getArgument(1);
                    if (arg12 instanceof TRSConstantTerm) {
                        Integer value1 = Integer.valueOf(((TRSConstantTerm)arg12).getValue());
                        Integer value2 = Integer.valueOf(((TRSConstantTerm)arg2).getValue());
                        if (value1 != null && value2 != null) {
                            Integer combinedValue = value1 + value2;

                            TRSTerm newConstant = TRSTerm.createConstant(combinedValue.toString());
                            return TRSTerm.createFunctionApplication(getBinaryMinus(), arg11, newConstant).simplify();
                        }
                    }
                }
            }
        }
        
        if (arg2 instanceof TRSFunctionApplication) {
            TRSFunctionApplication arg2FuncAppl = (TRSFunctionApplication)arg2;
            FunctionSymbol arg2FuncSymb = arg2FuncAppl.getFunctionSymbol();
            // Simplify (x - (-y)) to (x + y)
            if (arg2FuncSymb.equals(getUnaryMinus())) {
                return TRSTerm.createFunctionApplication(getBinaryPlus(), arg1, arg2FuncAppl.getArgument(0)).simplify();
            }
        }
        
        return this;
    }
    
    /**
     * Applies all simplification methods assuming this is a binary plus function
     * 
     * These simplifications are:
     * <ul>
     *   <li>Move constants to the start of term
     *   <li>Fold the addition of constants into one constant, e.g. (3 + 4) to (7)
     *   <li>Fold constant of this term with term of subterm, e.g. ((x + 1) + 4) to (x + 5)
     *   <li>Fold constant of this term with term of subterm, e.g. ((x - 1) + 4) to (x + 3)
     *   <li>Simplify (x + (-y)) to (x - y)
     * </ul>
     * 
     * @return A possibly simplified version of this term 
     */
    private TRSTerm simplifyBinaryPlus() {
        if (Globals.useAssertions) {
            assert getFunctionSymbol().equals(getBinaryPlus());
        }

        TRSTerm arg1 = getArgument(0);
        TRSTerm arg2 = getArgument(1);
        
        // Move constant term of plus to the back. Needed for further simplifications
        if (arg1 instanceof TRSConstantTerm && !(arg2 instanceof TRSConstantTerm)) {
            return TRSTerm.createFunctionApplication(getBinaryPlus(), arg2, arg1).simplify();
        }
        
        // Move constant in nested plus on the lhs to the right, e.g. (x + 1) + y -> (x + y) + 1 
        if (arg1 instanceof TRSFunctionApplication) {
            TRSFunctionApplication arg1FuncAppl = (TRSFunctionApplication) arg1;
            if (arg1FuncAppl.getFunctionSymbol().equals(getBinaryPlus()) && arg1FuncAppl.getArgument(1) instanceof TRSConstantTerm && !(arg2 instanceof TRSConstantTerm)) {
                TRSTerm subExpr = TRSTerm.createFunctionApplication(getBinaryPlus(), arg1FuncAppl.getArgument(0), arg2);
                return TRSTerm.createFunctionApplication(getBinaryPlus(), subExpr, arg1FuncAppl.getArgument(1)).simplify();
            }
        }

        if (arg2 instanceof TRSConstantTerm) {
            // Resolve constant terms, e.g. (3 + 4) to (7)
            if (arg1 instanceof TRSConstantTerm) {
                Integer value1 = Integer.valueOf(((TRSConstantTerm)arg1).getValue());
                Integer value2 = Integer.valueOf(((TRSConstantTerm)arg2).getValue());
                if (value1 != null && value2 != null) {
                    Integer combinedValue = value1 + value2;
                    return TRSTerm.createConstant(combinedValue.toString());
                }
            } else if (arg1 instanceof TRSFunctionApplication) {
                TRSFunctionApplication arg1FuncAppl = (TRSFunctionApplication)arg1;
                FunctionSymbol arg1FuncSymb = arg1FuncAppl.getFunctionSymbol();
                // Fold constant of this term with term of subterm, e.g. ((x + 1) + 4) to (x + 5)
                if (arg1FuncSymb.equals(getBinaryPlus())) {
                    TRSTerm arg11 = arg1FuncAppl.getArgument(0);
                    TRSTerm arg12 = arg1FuncAppl.getArgument(1);
                    if (arg12 instanceof TRSConstantTerm) {
                        Integer value1 = Integer.valueOf(((TRSConstantTerm)arg12).getValue());
                        Integer value2 = Integer.valueOf(((TRSConstantTerm)arg2).getValue());
                        if (value1 != null && value2 != null) {
                            Integer combinedValue = value1 + value2;

                            TRSTerm newConstant = TRSTerm.createConstant(combinedValue.toString());
                            return TRSTerm.createFunctionApplication(getBinaryPlus(), arg11, newConstant).simplify();
                        }
                    }
                }

                // Fold constant of this term with term of subterm, e.g. ((x - 1) + 4) to (x + 3)
                if (arg1FuncSymb.equals(getBinaryMinus())) {
                    TRSTerm arg11 = arg1FuncAppl.getArgument(0);
                    TRSTerm arg12 = arg1FuncAppl.getArgument(1);
                    if (arg12 instanceof TRSConstantTerm) {
                        Integer value1 = Integer.valueOf(((TRSConstantTerm)arg12).getValue());
                        Integer value2 = Integer.valueOf(((TRSConstantTerm)arg2).getValue());
                        if (value1 != null && value2 != null) {
                            Integer combinedValue = value2 - value1;

                            TRSTerm newConstant = TRSTerm.createConstant(combinedValue.toString());
                            return TRSTerm.createFunctionApplication(getBinaryMinus(), arg11, newConstant).simplify();
                        }
                    }
                }
            }
        }
        
        if (arg2 instanceof TRSFunctionApplication) {
            TRSFunctionApplication arg2FuncAppl = (TRSFunctionApplication)arg2;
            FunctionSymbol arg2FuncSymb = arg2FuncAppl.getFunctionSymbol();
            // Simplify (x + (-y)) to (x - y)
            if (arg2FuncSymb.equals(getUnaryMinus())) {
                return TRSTerm.createFunctionApplication(getBinaryMinus(), arg1, arg2FuncAppl.getArgument(0));
            }
        }
        
        return this;
    }
    
    @Override
    public TRSTerm simplify() {
        FunctionSymbol funcSymb = getFunctionSymbol();

        // First, descend to all subterms and simplify them
        TRSFunctionApplication simplifiedTerm = TRSTerm.createFunctionApplication(funcSymb, simplify(getArguments()));

        // Afterwards apply simplification for this function applications
        if (funcSymb.equals(getUnaryMinus())) {
            return simplifiedTerm.simplifyUnaryMinus();
        } else if (funcSymb.equals(getBinaryMinus())) {
            return simplifiedTerm.simplifyBinaryMinus();
        } else if (funcSymb.equals(getBinaryPlus())) {
            return simplifiedTerm.simplifyBinaryPlus();
        } else {
            return simplifiedTerm;
        }
    }

    @Override
    public TRSTerm unfoldConstantMultiplication(int upToConstant) {
        if (getFunctionSymbol().equals(getBinaryMult())) {
            TRSConstantTerm constant = null;
            TRSTerm variable = null;
            
            // Find the constant and the variable in the multiplication
            if (getArgument(0) instanceof TRSConstantTerm) {
                constant = (TRSConstantTerm)getArgument(0);
                variable = getArgument(1);
            } else if (getArgument(1) instanceof TRSConstantTerm) {
                variable = getArgument(0);
                constant = (TRSConstantTerm)getArgument(1);
            }
            
            // If constant is not null, one was found
            if (constant != null) {
                Integer constantValue = Integer.valueOf(constant.getValue());
                if (constantValue != null && constantValue <= upToConstant) {
                    if (constantValue == 0) {
                        // Replace multiplication by zero with zero
                        return TRSConstantTerm.createConstant("0");
                    } else if (constantValue > 0) {
                        // Build addition term
                        TRSTerm result = variable;
                        for (int i = 2; i <= constantValue; i++) {
                            List<TRSTerm> args = new ArrayList<>(2);
                            args.add(result);
                            args.add(variable);
                            result = TRSFunctionApplication.createFunctionApplication(getBinaryPlus(), args);
                        }
                        return result;
                    }
                }
            }
            return this;
            
        } else {
            // Create a new function application by unfolding constant multiplication in all subterms
            List<TRSTerm> updatedArgs = new ArrayList<TRSTerm>(getArguments());
            for (int i = 0; i < updatedArgs.size(); i++) {
                TRSTerm updatedTerm = updatedArgs.get(i).unfoldConstantMultiplication(upToConstant);
                updatedArgs.set(i, updatedTerm);
            }
            return TRSTerm.createFunctionApplication(getFunctionSymbol(), updatedArgs);
        }
    }
    
    public int countAnnos(Set<FunctionSymbol> annoSyms) {
        var count = 0;
        for (TRSTerm arg : this.getArguments()) {
            count += arg.countAnnos(annoSyms);
        }
        if(annoSyms.contains(this.getFunctionSymbol())) {
            return count + 1;
        } else {
            return count;
        }
    }
    
    public Set<TRSFunctionApplication> getAnnoSubterms(Map<FunctionSymbol, FunctionSymbol> deAnnoMap) {
        Set<TRSFunctionApplication> res = new HashSet<TRSFunctionApplication>();

        for (TRSTerm arg : this.getArguments()) {
            res.addAll(arg.getAnnoSubterms(deAnnoMap));
        }
        
        if (deAnnoMap.keySet().contains(this.getRootSymbol())) {
            Set<Position> poses = this.getPositions();
            poses.remove(Position.EPSILON);
            res.add((TRSFunctionApplication) this.renameAtAllMap(poses, deAnnoMap));
        }

        return res;
    }
}
