package aprove.input.Programs.idp;

import java.math.*;
import java.util.*;

import aprove.input.Generated.idp.analysis.*;
import aprove.input.Generated.idp.node.*;
import aprove.input.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * Parses a <code>PExpr</code> into a <code>Term</code>.
 *
 * @author noschinski
 *
 */
public class ExpressionParser {

    /**
     * Default suffix for integer expressions (if none was explicitly specified).
     */
    final protected String defaultSuffix;

    /**
     * Symbols which are declared to be Variables in this IDP.
     */
    final protected ImmutableSet<String> vars;

    /**
     * Parse errors.
     */
    final protected List<ParseError> errors;

    /**
     * Predefined functions mapping
     */
    final protected Map<ImmutablePair<Func, List<? extends Domain>>, FunctionSymbol> predefinedMapping;


    /** Wrapper class to return a FunctionSymbol or a string. */
    protected static class Atom {

        final public String name;
        final public FunctionSymbol sym;

        public Atom(String name) {
            this.name = name;
            this.sym = null;
        }

        public Atom(FunctionSymbol sym) {
            this.sym = sym;
            this.name = null;
        }

        @Override
        public String toString() {
            if (this.sym == null) {
                return this.name;
            } else {
                return this.sym.toString();
            }
        }
    }

    /**
     * Parses an AST <code>PExpr</code> into a <code>Term</code>.
     *
     * <p>This tree walker is designed to only be applied to
     * a <code>PExpr</code>, not other <code>Node</code>s.</p>
     *
     * <p>One instance may only used once.</p>
     *
     * @author noschinski
     *
     */
    protected class ExpressionPass extends DepthFirstAdapter {
        // FIXME: Make use of opts!

        /**
         * Arguments to the currently parsed function application.
         *
         * This stack is pushed to by <code>inAFuncappExpr</code>
         * and popped by <code>outAFuncappExpr</code>.
         */
        final protected Stack<ArrayList<TRSTerm>> levelArgs;

        /**
         * The last parsed atom.
         *
         * This stack is pushed to by <code>inAxxxAtom</code> methods
         * and popped by <code>outAFuncappExpr</code> or
         * <code>outAAtomExpr</code>.
         */
        final protected Stack<Atom> levelAtom;

        protected String lastSuffix;


        public ExpressionPass() {
            this.levelArgs = new Stack<ArrayList<TRSTerm>>();
            this.levelAtom = new Stack<Atom>();

            this.levelArgs.push(new ArrayList<TRSTerm>());
        }

        private void pushSymbol(FunctionSymbol fs) {
            this.levelAtom.push(new Atom(fs));
        }

        // FIXME
        @Override
        public void outAAtomExpr(AAtomExpr node) {
            Atom atom = this.levelAtom.pop();
            TRSTerm t;
            if (atom.name != null) {
                if (ExpressionParser.this.vars.contains(atom.name)) {
                    t = TRSTerm.createVariable(atom.name);
                } else {
                    FunctionSymbol fs = FunctionSymbol.create(atom.name, 0);
                    t = TRSTerm.createFunctionApplication(fs, TRSTerm.EMPTY_ARGS);
                }
            } else {
                t = TRSTerm.createFunctionApplication(atom.sym, TRSTerm.EMPTY_ARGS);
            }
            this.levelArgs.peek().add(t);
        }

        // FIXME
        @Override
        public void inAFuncappExpr(AFuncappExpr node) {
            this.levelArgs.push(new ArrayList<TRSTerm>());
        }

        // FIXME
        @Override
        public void outAFuncappExpr(AFuncappExpr node) {
            ImmutableArrayList<TRSTerm> args =
                ImmutableCreator.create(this.levelArgs.pop());

            Atom atom = this.levelAtom.pop();
            TRSTerm t;
            if (atom.name != null) {
                if (ExpressionParser.this.vars.contains(atom.name)) {
                    ParseError pe = new ParseError(ParseError.ERROR);
                    String errMsg = "The var " + atom.name +
                        " is a Variable but used as a FunctionSymbol.";
                    pe.setMessage(errMsg);
                    ExpressionParser.this.errors.add(pe);
                }
                FunctionSymbol fs =
                    FunctionSymbol.create(atom.name, args.size());
                t = TRSTerm.createFunctionApplication(fs, args);
            } else {
                if (atom.sym.getArity() != args.size()) {
                    ParseError pe = new ParseError(ParseError.ERROR);
                    String errMsg = "The predefined FunctionSymbol " + atom.sym +
                        " is used with wrong arity (" + args.size() + " instead of " +
                        atom.sym.getArity() + ").";
                    pe.setMessage(errMsg);
                    ExpressionParser.this.errors.add(pe);
                }
                t = TRSTerm.createFunctionApplication(atom.sym, args);
            }
            this.levelArgs.peek().add(t);
        }

        /**
         * Determines the suffix of the current atom.
         *
         * All atoms which allow a suffix have a Suffix sub node, so in
         * their out* method <code>this.lastSuffix</code> is set to an
         * up-to-date value.
         */
        @Override
        public void inASuffix(ASuffix node) {
            TSuffixData data = node.getSuffixData();
            if (data == null) {
                this.lastSuffix = null;
            } else {
                // For technical reasons, the parser returns the suffix
                // prepended with its '_' separator;
                this.lastSuffix = this.computeSuffix(node);
            }
        }

        @Override
        public void outABwandAtom(ABwandAtom node) {
            this.pushSymbol(this.getIntFuncSym(Func.Bwand, this.getSuffix()));
        }

        @Override
        public void outABwnotAtom(ABwnotAtom node) {
            this.pushSymbol(this.getIntFuncSym(Func.Bwnot, this.getSuffix()));
        }

        @Override
        public void outABworAtom(ABworAtom node) {
            this.pushSymbol(this.getIntFuncSym(Func.Bwor, this.getSuffix()));
        }

        @Override
        public void outABwxorAtom(ABwxorAtom node) {
            this.pushSymbol(this.getIntFuncSym(Func.Bwxor, this.getSuffix()));
        }

        @Override
        public void outALandAtom(ALandAtom node) {
            this.pushSymbol(this.getBoolFuncSym(Func.Land));
        }

        @Override
        public void outABoolAtom(ABoolAtom node) {
            /* We don't do anything here, because levelArgs is already
             * modified by inAFalseBool and inATrueBool. Exactly one of
             * these two methods is called exactly once for one call to
             * this method and never else, so the documented usage of
             * levelArgs is satisfied.
             */
        }

        @Override
        public void outACastAtom(ACastAtom node) {
            String from = this.computeSuffix((ASuffix)node.getFrom());
            String to = this.computeSuffix((ASuffix)node.getTo());
            this.pushSymbol(this.getIntFuncSym(Func.Cast, from + "@" + to));
        }

        @Override
        public void outADivAtom(ADivAtom node) {
            this.pushSymbol(this.getIntFuncSym(Func.Div, this.getSuffix()));
        }

        @Override
        public void outAEqAtom(AEqAtom node) {
            this.pushSymbol(this.getIntFuncSym(Func.Eq, this.getSuffix()));
        }

        @Override
        public void outANeqAtom(ANeqAtom node) {
            this.pushSymbol(this.getIntFuncSym(Func.Neq, this.getSuffix()));
        }

        @Override
        public void outAGeAtom(AGeAtom node) {
            this.pushSymbol(this.getIntFuncSym(Func.Ge, this.getSuffix()));
        }

        @Override
        public void outAGtAtom(AGtAtom node) {
            this.pushSymbol(this.getIntFuncSym(Func.Gt, this.getSuffix()));
        }

        @Override
        public void outAIntAtom(AIntAtom node) {
            String intstr = node.getInt().toString().trim();

            FunctionSymbol fs =
                this.getIntConstr(intstr, this.getSuffix());
            this.levelAtom.push(new Atom(fs));
        }

        @Override
        public void outALeAtom(ALeAtom node) {
            this.pushSymbol(this.getIntFuncSym(Func.Le, this.getSuffix()));
        }

        @Override
        public void outALtAtom(ALtAtom node) {
            this.pushSymbol(this.getIntFuncSym(Func.Lt, this.getSuffix()));
        }

        @Override
        public void outAMinusAtom(AMinusAtom node) {
            this.pushSymbol(this.getIntFuncSym(Func.Sub, this.getSuffix()));
        }

        @Override
        public void outALnotAtom(ALnotAtom node) {
            this.pushSymbol(this.getBoolFuncSym(Func.Lnot));
        }

        @Override
        public void outALorAtom(ALorAtom node) {
            this.pushSymbol(this.getBoolFuncSym(Func.Lor));
        }

        @Override
        public void outAPlusAtom(APlusAtom node) {
            this.pushSymbol(this.getIntFuncSym(Func.Add, this.getSuffix()));
        }

        @Override
        public void outAStarAtom(AStarAtom node) {
            this.pushSymbol(this.getIntFuncSym(Func.Mul, this.getSuffix()));
        }

        @Override
        public void outAModAtom(AModAtom node) {
            this.pushSymbol(this.getIntFuncSym(Func.Mod, this.getSuffix()));
        }

        @Override
        public void outAUnaryMinusAtom(AUnaryMinusAtom node) {
            this.pushSymbol(this.getIntFuncSym(Func.UnaryMinus, this.getSuffix()));
        }

        @Override
        public void outAVarAtom(AVarAtom node) {
            String name = node.toString().trim();
            name = EscapeHandler.unescape(name);
            this.levelAtom.push(new Atom(name));
        }

        @Override
        public void outAFalseBool(AFalseBool node) {
            this.pushSymbol(IDPPredefinedMap.DEFAULT_MAP.getBooleanFalse().getSym());
        }

        @Override
        public void outATrueBool(ATrueBool node) {
            this.pushSymbol(IDPPredefinedMap.DEFAULT_MAP.getBooleanTrue().getSym());
        }

        public TRSTerm getExpr() {
            return this.levelArgs.pop().get(0);
        }

        /**
         * Determine the suffix of an atom.
         *
         * This is either the supplied suffix as determined by {@link inASuffix}
         * or the default suffix.
         *
         * Note: Methods calling this methods must be sure to be called after
         * {@link inASuffix}, so they must be <code>outA*Atom</code> and not
         * <code>inA*Atom</code>.
         */
        private String getSuffix() {
            if (this.lastSuffix == null) {
                return ExpressionParser.this.defaultSuffix;
            } else {
                return this.lastSuffix;
            }
        }

        private FunctionSymbol getBoolFuncSym(Func func) {
            List<BooleanDomain> domains = new ArrayList<BooleanDomain>(func.getArity());
            for (int i = func.getArity() - 1; i>=0; i--) {
                domains.add(DomainFactory.BOOLEAN);
            }
            FunctionSymbol res = ExpressionParser.this.predefinedMapping.get(new ImmutablePair<Func, List<? extends BooleanDomain>>(func, domains));
            if (res != null) {
                return res;
            } else {
                // complete domain list
                res = FunctionSymbol.create(func.getName(), func.getArity());;
                ExpressionParser.this.predefinedMapping.put(new ImmutablePair<Func, List<? extends Domain>>(func, domains), res);
                return res;
            }
        }

        private FunctionSymbol getIntConstr(String intstr, String suffix) {
            List<? extends IntegerDomain> domains = this.getIntDomains(suffix);
            return PredefinedSemanticsFactory.getInt(BigIntImmutable.create(new BigInteger(intstr)), domains.get(0)).getSym();
        }

        private FunctionSymbol getIntFuncSym(Func func, String suffix) {
            List<? extends IntegerDomain> domains = this.getIntDomains(suffix);
            if (domains.size() == 1 && func.getArity() > 1) {
                ArrayList<IntegerDomain> newDomains = new ArrayList<IntegerDomain>(domains);
                IntegerDomain dom = domains.get(0);
                for (int i = func.getArity() - domains.size() - 1; i>=0; i--) {
                    newDomains.add(dom);
                }
                domains = newDomains;
            }
            FunctionSymbol res = ExpressionParser.this.predefinedMapping.get(new ImmutablePair<Func, List<? extends IntegerDomain>>(func, domains));
            if (res != null) {
                return res;
            } else {
                // complete domain list
                res = FunctionSymbol.create(func.getName(), func.getArity());
                ExpressionParser.this.predefinedMapping.put(new ImmutablePair<Func, List<? extends Domain>>(func, domains), res);
                return res;
            }
        }

        private List<? extends IntegerDomain> getIntDomains(String suffix) {
            String[] domains = suffix.split("@");
            ArrayList<IntegerDomain> res = new ArrayList<IntegerDomain>(domains.length);
            for (String domain : domains) {
                if (domain.equals("z") || domain.equals(DomainFactory.INTEGERS.getSuffix())) {
                    res.add(DomainFactory.INTEGERS);
                } else {
                    res.add(DomainFactory.createIntDomain(Integer.parseInt(domain)));
                }
            }
            if (res.isEmpty()) {
                res.add(DomainFactory.INTEGERS);
            }
            return res;
        }


        private String computeSuffix(ASuffix node) {
            return node.getSuffixData().toString().trim().substring(1);
        }

    }

    /**
     * @param vars
     *  Set of names considered to be a <code>Variable</code> instead of
     *  a <code>FunctionSymbol</code>
     * @param domains
     *  The set of integer (operation) suffixes used in this IDP. New domains
     *  are added to this set.
     * @param errors
     *  Occurring parse errors are added to this list.
     * @param predefinedMapping
     *  the mapping of predefined functions to function symbols
     */
    public ExpressionParser(ImmutableSet<String> vars,
            String defaultSuffix, List<ParseError> errors,
            Map<ImmutablePair<Func,List<? extends Domain>>, FunctionSymbol> predefinedMapping) {
        this.defaultSuffix = defaultSuffix;
        this.vars = vars;
        this.errors = errors;
        this.predefinedMapping = predefinedMapping;
    }

    /**
     * Parses an <code>PExpr</code> into a <code>Term</code>
     *
     * <p>On a parse error, an error is added to the parse error list,
     * but not signaled otherwise. In particular, a non-null
     * <code>Term</code> is always returned.</p>
     *
     * @param node PExpr to be parsed.
     * @return Term generated from this PExpr.
     */
    public TRSTerm parse(PExpr node) {
        ExpressionPass epass = new ExpressionPass();
        node.apply(epass);
        return epass.getExpr();
    }

}
