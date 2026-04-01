package aprove.input.Programs.prolog.processors;

import java.math.*;
import java.util.*;
import java.util.logging.*;

import aprove.input.Programs.prolog.*;
import aprove.input.Programs.prolog.structure.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;

/**
 * The IntegerArithmeticTransformer adds clauses for built-in integer
 * arithmetic and transforms integers in a term representation.<br><br>
 *
 * Created: Oct 23, 2006<br>
 * Last modified: May 31, 2011
 *
 * @author cryingshadow
 * @version $Id$
 */
@NoParams
public class IntegerArithmeticTransformer extends PrologProblemProcessor {

    /**
     * IntegerArithmeticTransformerProof.<br><br>
     *
     * Created: Nov 14, 2006<br>
     * Last modified: Nov 14, 2006
     *
     * @author cryingshadow
     * @version $Id$
     */
    public static class IntegerArithmeticTransformerProof extends DefaultProof {

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "Added definitions of predefined predicates " + o.cite(Citation.PROLOG) + ".";
        }

    }

    /**
     * IsSyntaxException.<br><br>
     *
     * Created: Nov 14, 2006<br>
     * Last modified: Nov 14, 2006
     *
     * @author cryingshadow
     * @version $Id$
     */
    public static class IsSyntaxException extends Exception {

        private static final long serialVersionUID = -6111233137860950931L;

        /**
         *
         */
        public IsSyntaxException() {
            super("Unexpected symbol occured in is predicate!");
        }

    }

    /**
     * GeqWalker.<br><br>
     *
     * Created: Nov 14, 2006<br>
     * Last modified: Nov 14, 2006
     *
     * @author cryingshadow
     * @version $Id$
     */
    private static class GeqWalker implements ReplacementWalker {

        private final FreshNameGenerator fridge;

        /**
         * @param f
         */
        public GeqWalker(final FreshNameGenerator f) {
            if (f == null) {
                throw new NullPointerException();
            }
            this.fridge = f;
        }

        @Override
        public boolean goDeeper(final PrologTerm term) {
            return true;
        }

        @Override
        public boolean isApplicable(final PrologTerm term) {
            return term != null && term.isGeq();
        }

        @Override
        public PrologTerm replace(final PrologTerm term) {
            final List<PrologTerm> first = new ArrayList<PrologTerm>();
            final List<PrologTerm> second = new ArrayList<PrologTerm>();
            final List<PrologTerm> gt = new ArrayList<PrologTerm>();
            final PrologNonAbstractVariable var1 = new PrologNonAbstractVariable(this.fridge.getFreshName("X", false));
            final PrologNonAbstractVariable var2 = new PrologNonAbstractVariable(this.fridge.getFreshName("X", false));
            first.add(var1);
            first.add(term.getArgument(0));
            second.add(var2);
            second.add(term.getArgument(1));
            gt.add(var1);
            gt.add(var2);
            try {
                return PrologTerms.createConjunction(
                    PrologTerms.createConjunction(
                        IntegerArithmeticTransformer.transformIs(new PrologTerm(PrologBuiltin.IS_NAME, first)),
                        IntegerArithmeticTransformer.transformIs(new PrologTerm(PrologBuiltin.IS_NAME, second))),
                    PrologTerms.createDisjunction(
                        new PrologTerm(IntegerArithmeticTransformer.GREATER, gt),
                        new PrologTerm(PrologBuiltin.UNIFY_NAME, gt)));
            } catch (final IsSyntaxException e) {
                IntegerArithmeticTransformer.logger.log(Level.INFO, "WARNING: >= predicate could not be transformed!");
            }
            return term;
        }

    }

    /**
     * GtWalker.<br><br>
     *
     * Created: Nov 14, 2006<br>
     * Last modified: Nov 14, 2006
     *
     * @author cryingshadow
     * @version $Id$
     */
    private static class GtWalker implements ReplacementWalker {

        private final FreshNameGenerator fridge;

        /**
         * @param f
         */
        public GtWalker(final FreshNameGenerator f) {
            if (f == null) {
                throw new NullPointerException();
            }
            this.fridge = f;
        }

        @Override
        public boolean goDeeper(final PrologTerm term) {
            return true;
        }

        @Override
        public boolean isApplicable(final PrologTerm term) {
            return term != null && term.isGreater();
        }

        @Override
        public PrologTerm replace(final PrologTerm term) {
            final List<PrologTerm> first = new ArrayList<PrologTerm>();
            final List<PrologTerm> second = new ArrayList<PrologTerm>();
            final List<PrologTerm> gt = new ArrayList<PrologTerm>();
            final PrologNonAbstractVariable var1 = new PrologNonAbstractVariable(this.fridge.getFreshName("X", false));
            final PrologNonAbstractVariable var2 = new PrologNonAbstractVariable(this.fridge.getFreshName("X", false));
            first.add(var1);
            first.add(term.getArgument(0));
            second.add(var2);
            second.add(term.getArgument(1));
            gt.add(var1);
            gt.add(var2);
            try {
                return PrologTerms.createConjunction(
                    PrologTerms.createConjunction(
                        IntegerArithmeticTransformer.transformIs(new PrologTerm(PrologBuiltin.IS_NAME, first)),
                        IntegerArithmeticTransformer.transformIs(new PrologTerm(PrologBuiltin.IS_NAME, second))),
                    new PrologTerm(IntegerArithmeticTransformer.GREATER, gt));
            } catch (final IsSyntaxException e) {
                IntegerArithmeticTransformer.logger.log(Level.INFO, "WARNING: > predicate could not be transformed!");
            }
            return term;
        }

    }

    /**
     * IntWalker.<br><br>
     *
     * Created: Nov 14, 2006<br>
     * Last modified: Nov 14, 2006
     *
     * @author cryingshadow
     * @version $Id$
     */
    private static class IntWalker implements ReplacementWalker {

        @Override
        public boolean goDeeper(final PrologTerm term) {
            return true;
        }

        @Override
        public boolean isApplicable(final PrologTerm term) {
            return term != null && term.isInt();
        }

        @Override
        public PrologTerm replace(final PrologTerm term) {
            return IntegerArithmeticTransformer.transformInts((PrologInt) term);
        }

    }

    /**
     * IsEqualWalker.<br><br>
     *
     * Created: Nov 14, 2006<br>
     * Last modified: Nov 14, 2006
     *
     * @author cryingshadow
     * @version $Id$
     */
    private static class IsEqualWalker implements ReplacementWalker {

        private final FreshNameGenerator fridge;

        /**
         * @param f
         */
        public IsEqualWalker(final FreshNameGenerator f) {
            if (f == null) {
                throw new NullPointerException();
            }
            this.fridge = f;
        }

        @Override
        public boolean goDeeper(final PrologTerm term) {
            return true;
        }

        @Override
        public boolean isApplicable(final PrologTerm term) {
            return term != null && term.isIsEqual();
        }

        @Override
        public PrologTerm replace(final PrologTerm term) {
            final PrologNonAbstractVariable var1 = new PrologNonAbstractVariable(this.fridge.getFreshName("X", false));
            final PrologNonAbstractVariable var2 = new PrologNonAbstractVariable(this.fridge.getFreshName("X", false));
            final List<PrologTerm> firstArgs = new ArrayList<PrologTerm>();
            final List<PrologTerm> secondArgs = new ArrayList<PrologTerm>();
            final List<PrologTerm> unifyArgs = new ArrayList<PrologTerm>();
            firstArgs.add(var1);
            firstArgs.add(term.getArgument(0));
            secondArgs.add(var2);
            secondArgs.add(term.getArgument(1));
            unifyArgs.add(var1);
            unifyArgs.add(var2);
            try {
                return PrologTerms.createConjunction(
                    PrologTerms.createConjunction(
                        IntegerArithmeticTransformer.transformIs(new PrologTerm(PrologBuiltin.IS_NAME, firstArgs)),
                        IntegerArithmeticTransformer.transformIs(new PrologTerm(PrologBuiltin.IS_NAME, secondArgs))),
                    new PrologTerm(PrologBuiltin.UNIFY_NAME, unifyArgs));
            } catch (final IsSyntaxException e) {
                IntegerArithmeticTransformer.logger.log(Level.INFO, "WARNING: =:= predicate could not be transformed!");
            }
            return term;
        }

    }

    /**
     * IsUnequalWalker.<br><br>
     *
     * Created: Nov 14, 2006<br>
     * Last modified: Nov 14, 2006
     *
     * @author cryingshadow
     * @version $Id$
     */
    private static class IsUnequalWalker implements ReplacementWalker {

        private final FreshNameGenerator fridge;

        /**
         * @param f
         */
        public IsUnequalWalker(final FreshNameGenerator f) {
            if (f == null) {
                throw new NullPointerException();
            }
            this.fridge = f;
        }

        @Override
        public boolean goDeeper(final PrologTerm term) {
            return true;
        }

        @Override
        public boolean isApplicable(final PrologTerm term) {
            return term != null && term.isIsUnequal();
        }

        @Override
        public PrologTerm replace(final PrologTerm term) {
            final List<PrologTerm> firstArgs = new ArrayList<PrologTerm>();
            final List<PrologTerm> secondArgs = new ArrayList<PrologTerm>();
            final List<PrologTerm> nounifyArgs = new ArrayList<PrologTerm>();
            final PrologNonAbstractVariable var1 = new PrologNonAbstractVariable(this.fridge.getFreshName("X", false));
            final PrologNonAbstractVariable var2 = new PrologNonAbstractVariable(this.fridge.getFreshName("X", false));
            firstArgs.add(var1);
            firstArgs.add(term.getArgument(0));
            secondArgs.add(var2);
            secondArgs.add(term.getArgument(1));
            nounifyArgs.add(var1);
            nounifyArgs.add(var2);
            try {
                return PrologTerms.createConjunction(
                    PrologTerms.createConjunction(
                        IntegerArithmeticTransformer.transformIs(new PrologTerm(PrologBuiltin.IS_NAME, firstArgs)),
                        IntegerArithmeticTransformer.transformIs(new PrologTerm(PrologBuiltin.IS_NAME, secondArgs))),
                    new PrologTerm(IntegerArithmeticTransformer.NOUNIFY, nounifyArgs));
            } catch (final IsSyntaxException e) {
                IntegerArithmeticTransformer.logger
                    .log(Level.INFO, "WARNING: =\\= predicate could not be transformed!");
            }
            return term;
        }

    }

    /**
     * LeqWalker.<br><br>
     *
     * Created: Nov 14, 2006<br>
     * Last modified: Nov 14, 2006
     *
     * @author cryingshadow
     * @version $Id$
     */
    private static class LeqWalker implements ReplacementWalker {

        private final FreshNameGenerator fridge;

        /**
         * @param f
         */
        public LeqWalker(final FreshNameGenerator f) {
            if (f == null) {
                throw new NullPointerException();
            }
            this.fridge = f;
        }

        @Override
        public boolean goDeeper(final PrologTerm term) {
            return true;
        }

        @Override
        public boolean isApplicable(final PrologTerm term) {
            return term != null && term.isLeq();
        }

        @Override
        public PrologTerm replace(final PrologTerm term) {
            final List<PrologTerm> first = new ArrayList<PrologTerm>();
            final List<PrologTerm> second = new ArrayList<PrologTerm>();
            final List<PrologTerm> ls = new ArrayList<PrologTerm>();
            final PrologNonAbstractVariable var1 = new PrologNonAbstractVariable(this.fridge.getFreshName("X", false));
            final PrologNonAbstractVariable var2 = new PrologNonAbstractVariable(this.fridge.getFreshName("X", false));
            first.add(var1);
            first.add(term.getArgument(0));
            second.add(var2);
            second.add(term.getArgument(1));
            ls.add(var1);
            ls.add(var2);
            try {
                return PrologTerms.createConjunction(
                    PrologTerms.createConjunction(
                        IntegerArithmeticTransformer.transformIs(new PrologTerm(PrologBuiltin.IS_NAME, first)),
                        IntegerArithmeticTransformer.transformIs(new PrologTerm(PrologBuiltin.IS_NAME, second))),
                    PrologTerms.createDisjunction(new PrologTerm(PrologBuiltin.UNIFY_NAME, ls), new PrologTerm(
                        IntegerArithmeticTransformer.LESS,
                        ls)));
            } catch (final IsSyntaxException e) {
                IntegerArithmeticTransformer.logger.log(Level.INFO, "WARNING: =< predicate could not be transformed!");
            }
            return term;
        }

    }

    /**
     * LsWalker.<br><br>
     *
     * Created: Nov 14, 2006<br>
     * Last modified: Nov 14, 2006
     *
     * @author cryingshadow
     * @version $Id$
     */
    private static class LsWalker implements ReplacementWalker {

        private final FreshNameGenerator fridge;

        /**
         * @param f
         */
        public LsWalker(final FreshNameGenerator f) {
            if (f == null) {
                throw new NullPointerException();
            }
            this.fridge = f;
        }

        @Override
        public boolean goDeeper(final PrologTerm term) {
            return true;
        }

        @Override
        public boolean isApplicable(final PrologTerm term) {
            return term != null && term.isLess();
        }

        @Override
        public PrologTerm replace(final PrologTerm term) {
            final List<PrologTerm> first = new ArrayList<PrologTerm>();
            final List<PrologTerm> second = new ArrayList<PrologTerm>();
            final List<PrologTerm> ls = new ArrayList<PrologTerm>();
            final PrologNonAbstractVariable var1 = new PrologNonAbstractVariable(this.fridge.getFreshName("X", false));
            final PrologNonAbstractVariable var2 = new PrologNonAbstractVariable(this.fridge.getFreshName("X", false));
            first.add(var1);
            first.add(term.getArgument(0));
            second.add(var2);
            second.add(term.getArgument(1));
            ls.add(var1);
            ls.add(var2);
            try {
                return PrologTerms.createConjunction(
                    PrologTerms.createConjunction(
                        IntegerArithmeticTransformer.transformIs(new PrologTerm(PrologBuiltin.IS_NAME, first)),
                        IntegerArithmeticTransformer.transformIs(new PrologTerm(PrologBuiltin.IS_NAME, second))),
                    new PrologTerm(IntegerArithmeticTransformer.LESS, ls));
            } catch (final IsSyntaxException e) {
                IntegerArithmeticTransformer.logger.log(Level.INFO, "WARNING: < predicate could not be transformed!");
            }
            return term;
        }

    }

    /**
     * The name of the predecessor constructor.
     */
    public static final String PRED = "pred";

    /**
     * The name of the successor constructor.
     */
    public static final String SUCC = "succ";

    /**
     * The name of the zero constant.
     */
    public static final String ZERO = "zero";

    protected static Logger logger = Logger.getLogger("aprove.verification.dpframework.PROLOGProblem.Processors");

    private static final String DIV = "isDiv";

    private static final String FAIL = "fail";

    private static final String GREATER = "isGreater";

    private static final String LESS = "isLess";

    /**
     * The maximal integer value that may occur in a program to be transformed
     * by this processor.
     */
    private static final BigInteger MAX_INT = BigInteger.valueOf(1000);

    private static final String MINUS = "isMinus";

    private static final String MODULO = "isModulo";

    private static final String NOUNIFY = "nounify";

    private static final String PLUS = "isPlus";

    private static final String TIMES = "isTimes";

    /**
     * Creates a set containing all names which may cause a conflict
     * when adding definitions for built-in predicates.
     * @return A set with all conflicting predicate names.
     */
    private static Set<String> getConflictNames(final PrologProgram prog) {
        final Set<String> used = new LinkedHashSet<String>();
        for (final FunctionSymbol sym : prog.createSetOfAllFunctionSymbols()) {
            used.add(sym.getName());
        }
        used.addAll(PrologBuiltins.BUILTIN_PREDICATE_NAMES);
        used.add(IntegerArithmeticTransformer.ZERO);
        used.add(IntegerArithmeticTransformer.SUCC);
        used.add(IntegerArithmeticTransformer.PRED);
        used.add(IntegerArithmeticTransformer.PLUS);
        used.add(IntegerArithmeticTransformer.MINUS);
        used.add(IntegerArithmeticTransformer.TIMES);
        used.add(IntegerArithmeticTransformer.DIV);
        used.add(IntegerArithmeticTransformer.NOUNIFY);
        used.add(IntegerArithmeticTransformer.MODULO);
        used.add(IntegerArithmeticTransformer.GREATER);
        used.add(IntegerArithmeticTransformer.LESS);
        used.add(IntegerArithmeticTransformer.FAIL);
        return used;
    }

    /**
     * @param conjunction
     * @param term
     * @param fridge
     * @return
     * @throws IsSyntaxException
     */
    private static PrologTerm isTransformation(
        final List<PrologTerm> conjunction,
        final PrologTerm term,
        final FreshNameGenerator fridge) throws IsSyntaxException
    {
        final int arity = term.getArity();
        final String name = term.getName();
        if (arity == 0
            || name.equals(IntegerArithmeticTransformer.ZERO)
            || name.equals(IntegerArithmeticTransformer.SUCC)
            || name.equals(IntegerArithmeticTransformer.PRED))
        {
            return term;
        }
        if (name.equals("+")) {
            if (arity == 2) {
                final List<PrologTerm> args = new ArrayList<PrologTerm>();
                args.add(IntegerArithmeticTransformer.isTransformation(conjunction, term.getArgument(0), fridge));
                args.add(IntegerArithmeticTransformer.isTransformation(conjunction, term.getArgument(1), fridge));
                final PrologNonAbstractVariable var = new PrologNonAbstractVariable(fridge.getFreshName("U", false));
                args.add(var);
                conjunction.add(new PrologTerm(IntegerArithmeticTransformer.PLUS, args));
                return var;
            }
            if (arity == 1) {
                return IntegerArithmeticTransformer.isTransformation(conjunction, term.getArgument(0), fridge);
            }
        } else if (name.equals("-")) {
            if (arity == 2) {
                final List<PrologTerm> args = new ArrayList<PrologTerm>();
                args.add(IntegerArithmeticTransformer.isTransformation(conjunction, term.getArgument(0), fridge));
                args.add(IntegerArithmeticTransformer.isTransformation(conjunction, term.getArgument(1), fridge));
                final PrologNonAbstractVariable var = new PrologNonAbstractVariable(fridge.getFreshName("U", false));
                args.add(var);
                conjunction.add(new PrologTerm(IntegerArithmeticTransformer.MINUS, args));
                return var;
            }
            if (arity == 1) {
                final List<PrologTerm> neg = new ArrayList<PrologTerm>();
                neg.add(new PrologTerm(IntegerArithmeticTransformer.ZERO));
                neg.add(IntegerArithmeticTransformer.isTransformation(conjunction, term.getArgument(0), fridge));
                final PrologNonAbstractVariable var = new PrologNonAbstractVariable(fridge.getFreshName("U", false));
                neg.add(var);
                conjunction.add(new PrologTerm(IntegerArithmeticTransformer.MINUS, neg));
                return var;
            }
        } else if (name.equals("*") && arity == 2) {
            final List<PrologTerm> args = new ArrayList<PrologTerm>();
            args.add(IntegerArithmeticTransformer.isTransformation(conjunction, term.getArgument(0), fridge));
            args.add(IntegerArithmeticTransformer.isTransformation(conjunction, term.getArgument(1), fridge));
            final PrologNonAbstractVariable var = new PrologNonAbstractVariable(fridge.getFreshName("U", false));
            args.add(var);
            conjunction.add(new PrologTerm(IntegerArithmeticTransformer.TIMES, args));
            return var;
        } else if (name.equals("//") && arity == 2) {
            final List<PrologTerm> args = new ArrayList<PrologTerm>();
            args.add(IntegerArithmeticTransformer.isTransformation(conjunction, term.getArgument(0), fridge));
            args.add(IntegerArithmeticTransformer.isTransformation(conjunction, term.getArgument(1), fridge));
            final PrologNonAbstractVariable var = new PrologNonAbstractVariable(fridge.getFreshName("U", false));
            args.add(var);
            conjunction.add(new PrologTerm(IntegerArithmeticTransformer.DIV, args));
            return var;
        } else if (name.equals("mod") && arity == 2) {
            final List<PrologTerm> args = new ArrayList<PrologTerm>();
            args.add(IntegerArithmeticTransformer.isTransformation(conjunction, term.getArgument(0), fridge));
            args.add(IntegerArithmeticTransformer.isTransformation(conjunction, term.getArgument(1), fridge));
            final PrologNonAbstractVariable var = new PrologNonAbstractVariable(fridge.getFreshName("U", false));
            args.add(var);
            conjunction.add(new PrologTerm(IntegerArithmeticTransformer.MODULO, args));
            return var;

        }
        throw new IsSyntaxException();
    }

    /**
     * @param clause
     */
    private static PrologClause isTransformation(final PrologClause clause) {
        return clause.walkBody(new ReplacementWalker() {

            @Override
            public boolean goDeeper(final PrologTerm term) {
                return true;
            }

            @Override
            public boolean isApplicable(final PrologTerm term) {
                return term != null && term.isIs();
            }

            @Override
            public PrologTerm replace(final PrologTerm term) {
                try {
                    return IntegerArithmeticTransformer.transformIs(term);
                } catch (final IsSyntaxException e) {
                    IntegerArithmeticTransformer.logger.log(
                        Level.INFO,
                        "WARNING: is predicate could not be transformed!");
                }
                return term;
            }

        });
    }

    /**
     * @param integer
     * @return
     */
    private static PrologTerm transformInts(final PrologInt integer) {
        final BigInteger value = integer.getValue();
        PrologTerm res = new PrologTerm(IntegerArithmeticTransformer.ZERO);
        if (value.compareTo(BigInteger.ZERO) < 0) {
            //                if (value < 1000) {
            //                    PrologTerm inf = new PrologTerm("..." + ((-value) - ((-value) % 1000)));
            //                    inf.add(res);
            //                    res = inf;
            //                }
            //                value = -((-value) % 1000);
            for (int i = 0; value.compareTo(BigInteger.valueOf(i)) < 0; i--) {
                final ArrayList<PrologTerm> args = new ArrayList<PrologTerm>();
                args.add(res);
                final PrologTerm pred = new PrologTerm(IntegerArithmeticTransformer.PRED, args);
                res = pred;
            }
        } else {
            //                if (value > 1000) {
            //                    PrologTerm inf = new PrologTerm("..." + (value - (value % 1000)));
            //                    inf.add(res);
            //                    res = inf;
            //                }
            //                value = value % 1000;
            for (int i = 0; value.compareTo(BigInteger.valueOf(i)) > 0; i++) {
                final ArrayList<PrologTerm> args = new ArrayList<PrologTerm>();
                args.add(res);
                final PrologTerm succ = new PrologTerm(IntegerArithmeticTransformer.SUCC, args);
                res = succ;
            }
        }
        return res;
    }

    /**
     * @param term
     * @return
     * @throws IsSyntaxException
     */
    private static PrologTerm transformIs(final PrologTerm term) throws IsSyntaxException {
        final List<PrologTerm> conjunction = new ArrayList<PrologTerm>();
        final List<PrologTerm> args = new ArrayList<PrologTerm>();
        args.add(term.getArgument(0));
        args.add(IntegerArithmeticTransformer.isTransformation(
            conjunction,
            term.getArgument(1),
            new FreshNameGenerator(FreshNameGenerator.PROLOG_VARS)));
        conjunction.add(new PrologTerm(PrologBuiltin.UNIFY_NAME, args));
        return PrologTerms.createConjunction(conjunction);
    }

    @Override
    public boolean isPrologApplicable(final PrologProblem pp) {
        return pp.getProgram().getBiggestAbsoluteNumber().compareTo(IntegerArithmeticTransformer.MAX_INT) <= 0
            && pp.getQuery().getPurpose().equals(PrologPurpose.TERMINATION);
    }

    @Override
    protected Result processPrologProblem(final PrologProblem pp, final Abortion aborter) throws AbortionException {
        final PrologProgram prog = pp.getProgram().copy();
        // flags to reduce redundant code
        boolean isTransformed = false;
        boolean existGreater = false;
        boolean existLess = false;
        List<PrologClause> oldClauses = prog.getClauses();
        List<PrologClause> newClauses = new ArrayList<PrologClause>();
        // first we have to solve name conflicts by renaming predicates
        // which would redefine built-in predicates
        final Set<FunctionSymbol> conflicts = prog.createSetOfDefinedPredicates();
        final Collection<FunctionSymbol> toRetain = new ArrayList<FunctionSymbol>(PrologBuiltins.BUILTIN_PREDICATES);
        // we leave the cut unchanged
        toRetain.remove(PrologBuiltin.CUT_PREDICATE);
        toRetain.add(FunctionSymbol.create(IntegerArithmeticTransformer.ZERO, 0));
        toRetain.add(FunctionSymbol.create(IntegerArithmeticTransformer.SUCC, 1));
        toRetain.add(FunctionSymbol.create(IntegerArithmeticTransformer.PRED, 1));
        toRetain.add(FunctionSymbol.create(IntegerArithmeticTransformer.FAIL, 1));
        toRetain.add(FunctionSymbol.create(IntegerArithmeticTransformer.PLUS, 3));
        toRetain.add(FunctionSymbol.create(IntegerArithmeticTransformer.MINUS, 3));
        toRetain.add(FunctionSymbol.create(IntegerArithmeticTransformer.TIMES, 3));
        toRetain.add(FunctionSymbol.create(IntegerArithmeticTransformer.DIV, 3));
        toRetain.add(FunctionSymbol.create(IntegerArithmeticTransformer.NOUNIFY, 2));
        toRetain.add(FunctionSymbol.create(IntegerArithmeticTransformer.GREATER, 2));
        toRetain.add(FunctionSymbol.create(IntegerArithmeticTransformer.LESS, 2));
        conflicts.retainAll(toRetain);
        final FreshNameGenerator fridge =
            new FreshNameGenerator(IntegerArithmeticTransformer.getConflictNames(prog), FreshNameGenerator.PROLOG_FUNCS);
        if (!conflicts.isEmpty()) {
            for (final FunctionSymbol sym : conflicts) {
                for (final PrologClause clause : oldClauses) {
                    newClauses.add(clause.rename(
                        sym.getName(),
                        sym.getArity(),
                        fridge.getFreshName(sym.getName(), true)));
                }
                oldClauses = newClauses;
                newClauses = new ArrayList<PrologClause>();
            }
        }
        // now we check the built-in predicates for occurence and add
        // clauses for them as necessary
        if (prog.hasPredicate(PrologBuiltin.ISEQUAL_PREDICATE)) {
            // "s =:= t" is transformed into "A is s, B is t, A = B".
            for (final PrologClause clause : oldClauses) {
                newClauses.add(clause.walkBody(new IsEqualWalker(new FreshNameGenerator(clause
                    .createSetOfAllVariableNames(), FreshNameGenerator.PROLOG_VARS))));
            }
            isTransformed = true;
            oldClauses = newClauses;
            newClauses = new ArrayList<PrologClause>();
        }
        if (prog.hasPredicate(PrologBuiltin.ISUNEQUAL_PREDICATE)) {
            // "s =\= t" is transformed in "A is s, B is t, nounify(A,B)".
            for (final PrologClause clause : oldClauses) {
                newClauses.add(clause.walkBody(new IsUnequalWalker(new FreshNameGenerator(clause
                    .createSetOfAllVariableNames(), FreshNameGenerator.PROLOG_VARS))));
            }
            /*
             * we add the following clause to the program:
             * nounify(X,Y) :- \+(X = Y).
             */
            final List<PrologTerm> nounifyArgs = new ArrayList<PrologTerm>();
            final List<PrologTerm> unifyArgs = new ArrayList<PrologTerm>();
            final List<PrologTerm> notArgs = new ArrayList<PrologTerm>();
            nounifyArgs.add(new PrologNonAbstractVariable("X"));
            nounifyArgs.add(new PrologNonAbstractVariable("Y"));
            unifyArgs.add(new PrologNonAbstractVariable("X"));
            unifyArgs.add(new PrologNonAbstractVariable("Y"));
            notArgs.add(new PrologTerm(PrologBuiltin.UNIFY_NAME, unifyArgs));
            newClauses.add(new PrologClause(
                new PrologTerm(IntegerArithmeticTransformer.NOUNIFY, nounifyArgs),
                new PrologTerm(PrologBuiltin.NOT_NAME, notArgs)));
            isTransformed = true;
            oldClauses = newClauses;
            newClauses = new ArrayList<PrologClause>();
        }
        if (prog.hasPredicate(PrologBuiltin.GEQ_PREDICATE)) {
            // "s >= t" is transformed in
            // "A is s, B is t, (isGreater(A,B) ; A = B)".
            for (final PrologClause clause : oldClauses) {
                newClauses.add(clause.walkBody(new GeqWalker(new FreshNameGenerator(clause
                    .createSetOfAllVariableNames(), FreshNameGenerator.PROLOG_VARS))));
            }
            existGreater = true;
            isTransformed = true;
            oldClauses = newClauses;
            newClauses = new ArrayList<PrologClause>();
        }
        if (prog.hasPredicate(PrologBuiltin.LEQ_PREDICATE)) {
            // "s =< t" is transformed in
            // "A is s, B is t, (isLess(A,B) ; A = B)".
            for (final PrologClause clause : oldClauses) {
                newClauses.add(clause.walkBody(new LeqWalker(new FreshNameGenerator(clause
                    .createSetOfAllVariableNames(), FreshNameGenerator.PROLOG_VARS))));
            }
            existLess = true;
            isTransformed = true;
            oldClauses = newClauses;
            newClauses = new ArrayList<PrologClause>();
        }
        if (prog.hasPredicate(PrologBuiltin.GREATER_PREDICATE)) {
            // "s > t" is transformed in
            // "A is s, B is t, isGreater(A,B)".
            for (final PrologClause clause : oldClauses) {
                newClauses.add(clause.walkBody(new GtWalker(new FreshNameGenerator(
                    clause.createSetOfAllVariableNames(),
                    FreshNameGenerator.PROLOG_VARS))));
            }
            existGreater = true;
            isTransformed = true;
            oldClauses = newClauses;
            newClauses = new ArrayList<PrologClause>();
        }
        if (prog.hasPredicate(PrologBuiltin.LESS_PREDICATE)) {
            // "s < t" is transformed in
            // "A is s, B is t, isLess(A,B)".
            for (final PrologClause clause : oldClauses) {
                newClauses.add(clause.walkBody(new LsWalker(new FreshNameGenerator(
                    clause.createSetOfAllVariableNames(),
                    FreshNameGenerator.PROLOG_VARS))));
            }
            existLess = true;
            isTransformed = true;
            oldClauses = newClauses;
            newClauses = new ArrayList<PrologClause>();
        }
        /*
         * =..(X,L)
         * //TODO ?
         */
        if (prog.hasPredicate(PrologBuiltin.IS_PREDICATE)) {
            /*
             * "s is t" is transformed in the way that all mathematical
             * operations in t are transformed in predicates, which
             * pass their computed values in new variables to each other
             * as they are used in outer operations. These predicate
             * calls are conjuncted in the order that innermost
             * operations come first and at last the new variable for
             * the value of the whole computation (let it be X) is used
             * in a predicate call "X = s".
             */
            for (final PrologClause clause : oldClauses) {
                newClauses.add(IntegerArithmeticTransformer.isTransformation(clause));
            }
            isTransformed = true;
            oldClauses = newClauses;
            newClauses = new ArrayList<PrologClause>();
        }
        if (isTransformed) {
            /*
             * If any is predicate has been transformed we have to add
             * clauses for the mathematical operations that can be
             * used to evaluate the second argument of the is predicate.
             * First we have to rename constructors used in the program
             * which may be conflicting to our new constructor terms.
             */
            for (final PrologClause clause : oldClauses) {
                newClauses.add(clause
                    .rename(
                        IntegerArithmeticTransformer.ZERO,
                        0,
                        fridge.getFreshName(IntegerArithmeticTransformer.ZERO, true))
                    .rename(
                        IntegerArithmeticTransformer.SUCC,
                        1,
                        fridge.getFreshName(IntegerArithmeticTransformer.SUCC, true))
                    .rename(
                        IntegerArithmeticTransformer.PRED,
                        1,
                        fridge.getFreshName(IntegerArithmeticTransformer.PRED, true)));
            }
            oldClauses = newClauses;
            newClauses = new ArrayList<PrologClause>();
            /*
             * Then we have to transform all integer values in a
             * constructor term representation, i.e. positive values
             * become succ(succ(...(zero)...)), negative values become
             * pred(pred(...(zero)...)) and 0 becomes zero.
             */
            final IntWalker walker = new IntWalker();
            for (final PrologClause clause : oldClauses) {
                newClauses.add(clause.walkAll(walker));
            }
            /*
             * Now we add the clauses for the mathematical operations:
             *
             * isPlus(zero,X,X).
             * isPlus(succ(X),zero,succ(X)).
             * isPlus(succ(X),succ(Y),succ(succ(Z))) :- isPlus(X,Y,Z).
             * isPlus(succ(X),pred(Y),Z) :- isPlus(X,Y,Z).
             * isPlus(pred(X),zero,pred(X)).
             * isPlus(pred(X),succ(Y),Z) :- isPlus(X,Y,Z).
             * isPlus(pred(X),pred(Y),pred(pred(Z))) :- isPlus(X,Y,Z).
             * isMinus(X,zero,X).
             * isMinus(zero,succ(Y),pred(Z)) :- isMinus(zero,Y,Z).
             * isMinus(zero,pred(Y),succ(Z)) :- isMinus(zero,Y,Z).
             * isMinus(succ(X),succ(Y),Z) :- isMinus(X,Y,Z).
             * isMinus(succ(X),pred(Y),succ(succ(Z))) :- isMinus(X,Y,Z).
             * isMinus(pred(X),succ(Y),pred(pred(Z))) :- isMinus(X,Y,Z).
             * isMinus(pred(X),pred(Y),Z) :- isMinus(X,Y,Z).
             * isTimes(X,zero,zero).
             * isTimes(zero,succ(Y),zero).
             * isTimes(zero,pred(Y),zero).
             * isTimes(succ(X),succ(Y),Z) :- isTimes(succ(X),Y,A), isPlus(A,succ(X),Z).
             * isTimes(succ(X),pred(Y),Z) :- isTimes(succ(X),Y,A), isMinus(A,succ(X),Z).
             * isTimes(pred(X),succ(Y),Z) :- isTimes(pred(X),Y,A), isPlus(A,pred(X),Z).
             * isTimes(pred(X),pred(Y),Z) :- isTimes(pred(X),Y,A), isMinus(A,pred(X),Z).
             * isDiv(zero,succ(Y),zero).
             * isDiv(zero,pred(Y),zero).
             * isDiv(succ(X),succ(Y),zero) :- isMinus(succ(X),succ(Y),pred(Z)).
             * isDiv(succ(X),succ(Y),succ(Z)) :- isMinus(succ(X),succ(Y),A),isDiv(A,succ(Y),Z).
             * isDiv(succ(X),pred(Y),Z) :- isMinus(zero,pred(Y),A), isDiv(succ(X),A,B), isMinus(zero,B,Z).
             * isDiv(pred(X),pred(Y),zero) :- isMinus(pred(X),pred(Y),succ(Z)).
             * isDiv(pred(X),pred(Y),succ(Z)) :- isMinus(pred(X),pred(Y),A),isDiv(A,pred(Y),Z).
             * isDiv(pred(X),succ(Y),Z) :- isMinus(zero,pred(X),A), isDiv(A,succ(Y),B), isMinus(zero,B,Z).
             * isModulo(X,Y,Z) :- isDiv(X,Y,A),isTimes(A,Y,B),isMinus(X,B,Z).
             */
            final PrologTerm x = new PrologNonAbstractVariable("X");
            final PrologTerm y = new PrologNonAbstractVariable("Y");
            final PrologTerm z = new PrologNonAbstractVariable("Z");
            final PrologTerm a = new PrologNonAbstractVariable("A");
            final PrologTerm b = new PrologNonAbstractVariable("B");
            final List<PrologTerm> xArg = new ArrayList<PrologTerm>();
            xArg.add(x);
            final List<PrologTerm> yArg = new ArrayList<PrologTerm>();
            yArg.add(y);
            final List<PrologTerm> zArg = new ArrayList<PrologTerm>();
            zArg.add(z);
            final List<PrologTerm> plus1 = new ArrayList<PrologTerm>();
            final List<PrologTerm> plus2 = new ArrayList<PrologTerm>();
            final List<PrologTerm> plus3 = new ArrayList<PrologTerm>();
            final List<PrologTerm> plus4 = new ArrayList<PrologTerm>();
            final List<PrologTerm> plus5 = new ArrayList<PrologTerm>();
            final List<PrologTerm> plus6 = new ArrayList<PrologTerm>();
            final List<PrologTerm> plus7 = new ArrayList<PrologTerm>();
            final List<PrologTerm> plusXYZArgs = new ArrayList<PrologTerm>();
            final List<PrologTerm> plusAS = new ArrayList<PrologTerm>();
            final List<PrologTerm> plusAP = new ArrayList<PrologTerm>();
            final List<PrologTerm> minus1 = new ArrayList<PrologTerm>();
            final List<PrologTerm> minus2 = new ArrayList<PrologTerm>();
            final List<PrologTerm> minus3 = new ArrayList<PrologTerm>();
            final List<PrologTerm> minus4 = new ArrayList<PrologTerm>();
            final List<PrologTerm> minus5 = new ArrayList<PrologTerm>();
            final List<PrologTerm> minus6 = new ArrayList<PrologTerm>();
            final List<PrologTerm> minus7 = new ArrayList<PrologTerm>();
            final List<PrologTerm> minusXYZArgs = new ArrayList<PrologTerm>();
            final List<PrologTerm> minus0YZArgs = new ArrayList<PrologTerm>();
            final List<PrologTerm> minusAS = new ArrayList<PrologTerm>();
            final List<PrologTerm> minusAP = new ArrayList<PrologTerm>();
            final List<PrologTerm> minusSSP = new ArrayList<PrologTerm>();
            final List<PrologTerm> minusSSA = new ArrayList<PrologTerm>();
            final List<PrologTerm> minus0pYA = new ArrayList<PrologTerm>();
            final List<PrologTerm> minus0BZArgs = new ArrayList<PrologTerm>();
            final List<PrologTerm> minusPPS = new ArrayList<PrologTerm>();
            final List<PrologTerm> minusPPA = new ArrayList<PrologTerm>();
            final List<PrologTerm> minus0pXA = new ArrayList<PrologTerm>();
            final List<PrologTerm> minusXBZ = new ArrayList<PrologTerm>();
            final List<PrologTerm> times1 = new ArrayList<PrologTerm>();
            final List<PrologTerm> times2 = new ArrayList<PrologTerm>();
            final List<PrologTerm> times3 = new ArrayList<PrologTerm>();
            final List<PrologTerm> times4 = new ArrayList<PrologTerm>();
            final List<PrologTerm> times5 = new ArrayList<PrologTerm>();
            final List<PrologTerm> times6 = new ArrayList<PrologTerm>();
            final List<PrologTerm> times7 = new ArrayList<PrologTerm>();
            final List<PrologTerm> timesS = new ArrayList<PrologTerm>();
            final List<PrologTerm> timesP = new ArrayList<PrologTerm>();
            final List<PrologTerm> timesAYB = new ArrayList<PrologTerm>();
            final List<PrologTerm> div1 = new ArrayList<PrologTerm>();
            final List<PrologTerm> div2 = new ArrayList<PrologTerm>();
            final List<PrologTerm> div3 = new ArrayList<PrologTerm>();
            final List<PrologTerm> div4 = new ArrayList<PrologTerm>();
            final List<PrologTerm> div5 = new ArrayList<PrologTerm>();
            final List<PrologTerm> div6 = new ArrayList<PrologTerm>();
            final List<PrologTerm> div7 = new ArrayList<PrologTerm>();
            final List<PrologTerm> div8 = new ArrayList<PrologTerm>();
            final List<PrologTerm> divASZ = new ArrayList<PrologTerm>();
            final List<PrologTerm> divSAB = new ArrayList<PrologTerm>();
            final List<PrologTerm> divAPZ = new ArrayList<PrologTerm>();
            final List<PrologTerm> divASB = new ArrayList<PrologTerm>();
            final List<PrologTerm> divXYA = new ArrayList<PrologTerm>();
            final List<PrologTerm> modulo = new ArrayList<PrologTerm>();
            final PrologTerm zero = new PrologTerm(IntegerArithmeticTransformer.ZERO);
            final List<PrologTerm> ssZArg = new ArrayList<PrologTerm>();
            final List<PrologTerm> ppZArg = new ArrayList<PrologTerm>();
            final PrologTerm succX = new PrologTerm(IntegerArithmeticTransformer.SUCC, xArg);
            final PrologTerm succY = new PrologTerm(IntegerArithmeticTransformer.SUCC, yArg);
            final PrologTerm succZ = new PrologTerm(IntegerArithmeticTransformer.SUCC, zArg);
            final PrologTerm predX = new PrologTerm(IntegerArithmeticTransformer.PRED, xArg);
            final PrologTerm predY = new PrologTerm(IntegerArithmeticTransformer.PRED, yArg);
            final PrologTerm predZ = new PrologTerm(IntegerArithmeticTransformer.PRED, zArg);
            ssZArg.add(succZ);
            final PrologTerm ssZ = new PrologTerm(IntegerArithmeticTransformer.SUCC, ssZArg);
            ppZArg.add(predZ);
            final PrologTerm ppZ = new PrologTerm(IntegerArithmeticTransformer.PRED, ppZArg);
            plus1.add(zero);
            plus1.add(x);
            plus1.add(x);
            plus2.add(succX);
            plus2.add(zero);
            plus2.add(succX);
            plus3.add(succX);
            plus3.add(succY);
            plus3.add(ssZ);
            plus4.add(succX);
            plus4.add(predY);
            plus4.add(z);
            plus5.add(predX);
            plus5.add(zero);
            plus5.add(predX);
            plus6.add(predX);
            plus6.add(succY);
            plus6.add(z);
            plus7.add(predX);
            plus7.add(predY);
            plus7.add(ppZ);
            plusXYZArgs.add(x);
            plusXYZArgs.add(y);
            plusXYZArgs.add(z);
            plusAS.add(a);
            plusAS.add(succX);
            plusAS.add(z);
            plusAP.add(a);
            plusAP.add(predX);
            plusAP.add(z);
            minus1.add(x);
            minus1.add(zero);
            minus1.add(x);
            minus2.add(zero);
            minus2.add(succY);
            minus2.add(predZ);
            minus3.add(zero);
            minus3.add(predY);
            minus3.add(succZ);
            minus4.add(succX);
            minus4.add(succY);
            minus4.add(z);
            minus5.add(succX);
            minus5.add(predY);
            minus5.add(ssZ);
            minus6.add(predX);
            minus6.add(succY);
            minus6.add(ppZ);
            minus7.add(predX);
            minus7.add(predY);
            minus7.add(z);
            minus0YZArgs.add(zero);
            minus0YZArgs.add(y);
            minus0YZArgs.add(z);
            minusXYZArgs.add(x);
            minusXYZArgs.add(y);
            minusXYZArgs.add(z);
            minusAS.add(a);
            minusAS.add(succX);
            minusAS.add(z);
            minusAP.add(a);
            minusAP.add(predX);
            minusAP.add(z);
            minusSSP.add(succX);
            minusSSP.add(succY);
            minusSSP.add(predZ);
            minusSSA.add(succX);
            minusSSA.add(succY);
            minusSSA.add(a);
            minus0pYA.add(zero);
            minus0pYA.add(predY);
            minus0pYA.add(a);
            minus0BZArgs.add(zero);
            minus0BZArgs.add(b);
            minus0BZArgs.add(z);
            minusPPS.add(predX);
            minusPPS.add(predY);
            minusPPS.add(succZ);
            minusPPA.add(predX);
            minusPPA.add(predY);
            minusPPA.add(a);
            minus0pXA.add(zero);
            minus0pXA.add(predX);
            minus0pXA.add(a);
            minusXBZ.add(x);
            minusXBZ.add(b);
            minusXBZ.add(z);
            times1.add(x);
            times1.add(zero);
            times1.add(zero);
            times2.add(zero);
            times2.add(succY);
            times2.add(zero);
            times3.add(zero);
            times3.add(predY);
            times3.add(zero);
            times4.add(succX);
            times4.add(succY);
            times4.add(z);
            times5.add(succX);
            times5.add(predY);
            times5.add(z);
            times6.add(predX);
            times6.add(succY);
            times6.add(z);
            times7.add(predX);
            times7.add(predY);
            times7.add(z);
            timesS.add(succX);
            timesS.add(y);
            timesS.add(a);
            timesP.add(predX);
            timesP.add(y);
            timesP.add(a);
            timesAYB.add(a);
            timesAYB.add(y);
            timesAYB.add(b);
            div1.add(zero);
            div1.add(succY);
            div1.add(zero);
            div2.add(zero);
            div2.add(predY);
            div2.add(zero);
            div3.add(succX);
            div3.add(succY);
            div3.add(zero);
            div4.add(succX);
            div4.add(succY);
            div4.add(succZ);
            div5.add(succX);
            div5.add(predY);
            div5.add(z);
            div6.add(predX);
            div6.add(predY);
            div6.add(zero);
            div7.add(predX);
            div7.add(predY);
            div7.add(succZ);
            div8.add(predX);
            div8.add(succY);
            div8.add(z);
            divASZ.add(a);
            divASZ.add(succY);
            divASZ.add(z);
            divSAB.add(succX);
            divSAB.add(a);
            divSAB.add(b);
            divAPZ.add(a);
            divAPZ.add(predY);
            divAPZ.add(z);
            divASB.add(a);
            divASB.add(succY);
            divASB.add(b);
            divXYA.add(x);
            divXYA.add(y);
            divXYA.add(a);
            modulo.add(x);
            modulo.add(y);
            modulo.add(z);
            final PrologTerm conMul4 =
                PrologTerms.createConjunction(
                    new PrologTerm(IntegerArithmeticTransformer.TIMES, timesS),
                    new PrologTerm(IntegerArithmeticTransformer.PLUS, plusAS));
            final PrologTerm conMul5 =
                PrologTerms.createConjunction(
                    new PrologTerm(IntegerArithmeticTransformer.TIMES, timesS),
                    new PrologTerm(IntegerArithmeticTransformer.MINUS, minusAS));
            final PrologTerm conMul6 =
                PrologTerms.createConjunction(
                    new PrologTerm(IntegerArithmeticTransformer.TIMES, timesP),
                    new PrologTerm(IntegerArithmeticTransformer.PLUS, plusAP));
            final PrologTerm conMul7 =
                PrologTerms.createConjunction(
                    new PrologTerm(IntegerArithmeticTransformer.TIMES, timesP),
                    new PrologTerm(IntegerArithmeticTransformer.MINUS, minusAP));
            final PrologTerm conDiv4 =
                PrologTerms.createConjunction(
                    new PrologTerm(IntegerArithmeticTransformer.MINUS, minusSSA),
                    new PrologTerm(IntegerArithmeticTransformer.DIV, divASZ));
            final PrologTerm plusXYZ = new PrologTerm(IntegerArithmeticTransformer.PLUS, plusXYZArgs);
            final PrologTerm minusXYZ = new PrologTerm(IntegerArithmeticTransformer.MINUS, minusXYZArgs);
            final PrologTerm minus0YZ = new PrologTerm(IntegerArithmeticTransformer.MINUS, minus0YZArgs);
            final PrologTerm minus0BZ = new PrologTerm(IntegerArithmeticTransformer.MINUS, minus0BZArgs);
            final List<PrologTerm> list5 = new ArrayList<PrologTerm>();
            final List<PrologTerm> list8 = new ArrayList<PrologTerm>();
            final List<PrologTerm> modList = new ArrayList<PrologTerm>();
            list5.add(new PrologTerm(IntegerArithmeticTransformer.MINUS, minus0pYA));
            list5.add(new PrologTerm(IntegerArithmeticTransformer.DIV, divSAB));
            list5.add(minus0BZ);
            list8.add(new PrologTerm(IntegerArithmeticTransformer.MINUS, minus0pXA));
            list8.add(new PrologTerm(IntegerArithmeticTransformer.DIV, divASB));
            list8.add(minus0BZ);
            modList.add(new PrologTerm(IntegerArithmeticTransformer.DIV, divXYA));
            modList.add(new PrologTerm(IntegerArithmeticTransformer.TIMES, timesAYB));
            modList.add(new PrologTerm(IntegerArithmeticTransformer.MINUS, minusXBZ));
            final PrologTerm conDiv5 = PrologTerms.createConjunction(list5);
            final PrologTerm conDiv7 =
                PrologTerms.createConjunction(
                    new PrologTerm(IntegerArithmeticTransformer.MINUS, minusPPA),
                    new PrologTerm(IntegerArithmeticTransformer.DIV, divAPZ));
            final PrologTerm conDiv8 = PrologTerms.createConjunction(list8);
            final PrologTerm conMod = PrologTerms.createConjunction(modList);
            newClauses.add(new PrologClause(new PrologTerm(IntegerArithmeticTransformer.PLUS, plus1), null));
            newClauses.add(new PrologClause(new PrologTerm(IntegerArithmeticTransformer.PLUS, plus2), null));
            newClauses.add(new PrologClause(new PrologTerm(IntegerArithmeticTransformer.PLUS, plus3), plusXYZ));
            newClauses.add(new PrologClause(new PrologTerm(IntegerArithmeticTransformer.PLUS, plus4), plusXYZ));
            newClauses.add(new PrologClause(new PrologTerm(IntegerArithmeticTransformer.PLUS, plus5), null));
            newClauses.add(new PrologClause(new PrologTerm(IntegerArithmeticTransformer.PLUS, plus6), plusXYZ));
            newClauses.add(new PrologClause(new PrologTerm(IntegerArithmeticTransformer.PLUS, plus7), plusXYZ));
            newClauses.add(new PrologClause(new PrologTerm(IntegerArithmeticTransformer.MINUS, minus1), null));
            newClauses.add(new PrologClause(new PrologTerm(IntegerArithmeticTransformer.MINUS, minus2), minus0YZ));
            newClauses.add(new PrologClause(new PrologTerm(IntegerArithmeticTransformer.MINUS, minus3), minus0YZ));
            newClauses.add(new PrologClause(new PrologTerm(IntegerArithmeticTransformer.MINUS, minus4), minusXYZ));
            newClauses.add(new PrologClause(new PrologTerm(IntegerArithmeticTransformer.MINUS, minus5), minusXYZ));
            newClauses.add(new PrologClause(new PrologTerm(IntegerArithmeticTransformer.MINUS, minus6), minusXYZ));
            newClauses.add(new PrologClause(new PrologTerm(IntegerArithmeticTransformer.MINUS, minus7), minusXYZ));
            newClauses.add(new PrologClause(new PrologTerm(IntegerArithmeticTransformer.TIMES, times1), null));
            newClauses.add(new PrologClause(new PrologTerm(IntegerArithmeticTransformer.TIMES, times2), null));
            newClauses.add(new PrologClause(new PrologTerm(IntegerArithmeticTransformer.TIMES, times3), null));
            newClauses.add(new PrologClause(new PrologTerm(IntegerArithmeticTransformer.TIMES, times4), conMul4));
            newClauses.add(new PrologClause(new PrologTerm(IntegerArithmeticTransformer.TIMES, times5), conMul5));
            newClauses.add(new PrologClause(new PrologTerm(IntegerArithmeticTransformer.TIMES, times6), conMul6));
            newClauses.add(new PrologClause(new PrologTerm(IntegerArithmeticTransformer.TIMES, times7), conMul7));
            newClauses.add(new PrologClause(new PrologTerm(IntegerArithmeticTransformer.DIV, div1), null));
            newClauses.add(new PrologClause(new PrologTerm(IntegerArithmeticTransformer.DIV, div2), null));
            newClauses.add(new PrologClause(new PrologTerm(IntegerArithmeticTransformer.DIV, div3), new PrologTerm(
                IntegerArithmeticTransformer.MINUS,
                minusSSP)));
            newClauses.add(new PrologClause(new PrologTerm(IntegerArithmeticTransformer.DIV, div4), conDiv4));
            newClauses.add(new PrologClause(new PrologTerm(IntegerArithmeticTransformer.DIV, div5), conDiv5));
            newClauses.add(new PrologClause(new PrologTerm(IntegerArithmeticTransformer.DIV, div6), new PrologTerm(
                IntegerArithmeticTransformer.MINUS,
                minusPPS)));
            newClauses.add(new PrologClause(new PrologTerm(IntegerArithmeticTransformer.DIV, div7), conDiv7));
            newClauses.add(new PrologClause(new PrologTerm(IntegerArithmeticTransformer.DIV, div8), conDiv8));
            newClauses.add(new PrologClause(new PrologTerm(IntegerArithmeticTransformer.MODULO, modulo), conMod));
            if (existGreater) {
                /*
                 * we add clauses for the isGreater predicate:
                 * isGreater(succ(X),zero).
                 * isGreater(succ(X),pred(Y)).
                 * isGreater(succ(X),succ(Y)) :- isGreater(X,Y).
                 * isGreater(zero,pred(Y)).
                 * isGreater(pred(X),pred(Y)) :- isGreater(X,Y).
                 */
                final List<PrologTerm> gt1 = new ArrayList<PrologTerm>();
                final List<PrologTerm> gt2 = new ArrayList<PrologTerm>();
                final List<PrologTerm> gt3 = new ArrayList<PrologTerm>();
                final List<PrologTerm> gt4 = new ArrayList<PrologTerm>();
                final List<PrologTerm> gt5 = new ArrayList<PrologTerm>();
                final List<PrologTerm> gtXYArgs = new ArrayList<PrologTerm>();
                gt1.add(succX);
                gt1.add(zero);
                gt2.add(succX);
                gt2.add(predY);
                gt3.add(succX);
                gt3.add(succY);
                gt4.add(zero);
                gt4.add(predY);
                gt5.add(predX);
                gt5.add(predY);
                gtXYArgs.add(x);
                gtXYArgs.add(y);
                final PrologTerm gtXY = new PrologTerm(IntegerArithmeticTransformer.GREATER, gtXYArgs);
                newClauses.add(new PrologClause(new PrologTerm(IntegerArithmeticTransformer.GREATER, gt1), null));
                newClauses.add(new PrologClause(new PrologTerm(IntegerArithmeticTransformer.GREATER, gt2), null));
                newClauses.add(new PrologClause(new PrologTerm(IntegerArithmeticTransformer.GREATER, gt3), gtXY));
                newClauses.add(new PrologClause(new PrologTerm(IntegerArithmeticTransformer.GREATER, gt4), null));
                newClauses.add(new PrologClause(new PrologTerm(IntegerArithmeticTransformer.GREATER, gt5), gtXY));
            }
            if (existLess) {
                /*
                 * we add clauses for the isLess predicate:
                 * isLess(pred(X),zero).
                 * isLess(pred(X),succ(Y)).
                 * isLess(pred(X),pred(Y)) :- isLess(X,Y).
                 * isLess(zero,succ(X)).
                 * isLess(succ(X),succ(Y)) :- isLess(X,Y).
                 */
                final List<PrologTerm> ls1 = new ArrayList<PrologTerm>();
                final List<PrologTerm> ls2 = new ArrayList<PrologTerm>();
                final List<PrologTerm> ls3 = new ArrayList<PrologTerm>();
                final List<PrologTerm> ls4 = new ArrayList<PrologTerm>();
                final List<PrologTerm> ls5 = new ArrayList<PrologTerm>();
                final List<PrologTerm> lsXYArgs = new ArrayList<PrologTerm>();
                ls1.add(predX);
                ls1.add(zero);
                ls2.add(predX);
                ls2.add(succY);
                ls3.add(predX);
                ls3.add(predY);
                ls4.add(zero);
                ls4.add(succY);
                ls5.add(succX);
                ls5.add(succY);
                lsXYArgs.add(x);
                lsXYArgs.add(y);
                final PrologTerm lsXY = new PrologTerm(IntegerArithmeticTransformer.LESS, lsXYArgs);
                newClauses.add(new PrologClause(new PrologTerm(IntegerArithmeticTransformer.LESS, ls1), null));
                newClauses.add(new PrologClause(new PrologTerm(IntegerArithmeticTransformer.LESS, ls2), null));
                newClauses.add(new PrologClause(new PrologTerm(IntegerArithmeticTransformer.LESS, ls3), lsXY));
                newClauses.add(new PrologClause(new PrologTerm(IntegerArithmeticTransformer.LESS, ls4), null));
                newClauses.add(new PrologClause(new PrologTerm(IntegerArithmeticTransformer.LESS, ls5), lsXY));
            }
            prog.getClauses().clear();
            prog.getClauses().addAll(newClauses);
            prog.flattenOutConjunctions();
            return
                ResultFactory.proved(
                    new PrologProblem(prog, pp.getQuery(), pp.getSMTFactory(), pp.getSMTLogic()),
                    YNMImplication.SOUND,
                    new IntegerArithmeticTransformerProof()
                );
        } else {
            return ResultFactory.unsuccessful();
        }
    }

}
