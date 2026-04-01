/*
 * Created on 14.07.2008
 */
package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Class to transform outermost TRSs into standard TRSs
 *
 * @version $Id$
 * @author thiemann
 *
 *
 */
public class OTRSToQTRSProcessor extends OTRSProcessor {

    private final Transformation transformation;

    @ParamsViaArgumentObject
    public OTRSToQTRSProcessor(final Arguments arguments) {
        this.transformation = arguments.transformation;
    }

    @Override
    public Result processOTRS(final OTRSProblem otrs, final Abortion aborter, final RuntimeInformation rti)
            throws AbortionException {
        // changed by Sebastian Weise (GeneralizedRules !)
        // we continue only if there are no "real" Generalized Rules in otrs !
        final Set<Rule> simpleRules = new LinkedHashSet<Rule>();
        for (final GeneralizedRule actGeneralizedRule : otrs.getR()) {
            if (actGeneralizedRule instanceof Rule) {
                simpleRules.add((Rule) actGeneralizedRule);
            } else {
                assert (false);
                return ResultFactory.unsuccessful();
            }
        }
        final Set<Rule> rules = ImmutableCreator.create(simpleRules);

        final Set<FunctionSymbol> signature = CollectionUtils
                .getFunctionSymbols(rules);
        final Quadruple<Set<Rule>, Boolean, YNMImplication, QTRSProof> newProblem =
            this.transformation
                .getTransformed(rules, signature);

        if (newProblem != null) {

            QTRSProblem qtrs;
            if (newProblem.x) {
                final Set<Rule> newRules = newProblem.w;
                qtrs = QTRSProblem.create(ImmutableCreator.create(newRules),
                        CollectionUtils.getLeftHandSides(newRules));
            } else {
                qtrs = QTRSProblem
                        .create(ImmutableCreator.create(newProblem.w));
            }
            return ResultFactory.proved(qtrs, newProblem.y, newProblem.z);
        } else {
            return ResultFactory.unsuccessful();
        }

    }

    @Override
    public boolean isOTRSApplicable(final OTRSProblem otrs) {
        if (Options.certifier.isCeta()) {
            return false;
        }
        // changed by Sebastian Weise (GeneralizedRules !)
        // we continue only if there are no "real" Generalized Rules in otrs !
        // Zantema + Thiemann not applicable for fresh variables in rhs's;
        // trivial just sound, so free variables are problematic
        for (final GeneralizedRule actGeneralizedRule : otrs.getR()) {
            if (!(actGeneralizedRule instanceof Rule)) {
                return false;
            }
        }
        return this.transformation.isApplicable(otrs);
    }

    @SuppressWarnings("serial")
    private static class VariableConditionException extends Exception {
    };

    private static final VariableConditionException VAR_COND = new VariableConditionException();

    /**
     * now here are all the transformations given.
     * @author thiemann
     *
     */
    private static enum Transformation {

        /**
         * the trivial transformation just ignores the outermost strategy
         */

        Trivial {
            @Override
            public String cite(final Export_Util eu) {
                return "";
            }

            @Override
            public Quadruple<Set<Rule>, Boolean, YNMImplication, QTRSProof> getTransformed(
                    final Set<Rule> R, final Set<FunctionSymbol> signature) {
                final boolean innermost = false;
                return new Quadruple<Set<Rule>, Boolean, YNMImplication, QTRSProof>(
                        R, innermost, YNMImplication.SOUND,
                        new TransformationProof(R, this, innermost));
            }

            @Override
            public boolean isApplicable(final OTRSProblem otrs) {
                return true;
            }
        },

        /**
         * the thiemann-transformation transforms to innermost
         */
        Thiemann {
            @Override
            public String toString() {
                return "Thiemann";
            }

            @Override
            public String cite(final Export_Util eu) {
                return ""; // TODO publish a paper :-)
            }

            @Override
            public Quadruple<Set<Rule>, Boolean, YNMImplication, QTRSProof> getTransformed(
                    final Set<Rule> R, final Set<FunctionSymbol> sig) {
                final int sigSize = sig.size();
                final int roughlyNewSize = 3 * sigSize + 4 + sigSize * 2; // the last 2 is considered to be the average arity for the in_f_i's
                final FunctionSymbolGenerator funSymGen = new FunctionSymbolGenerator(
                        roughlyNewSize);
                // first copy the original signature
                for (final FunctionSymbol f : sig) {
                    final FunctionSymbol g = funSymGen.getFresh(f.getName(), f
                            .getArity());
                    if (Globals.useAssertions) {
                        assert (f.equals(g));
                    }
                }
                // then create the new unique symbols
                final FunctionSymbol top = funSymGen.getFresh("top", 1);
                final FunctionSymbol goup = funSymGen.getFresh("go_up", 1);
                final FunctionSymbol result = funSymGen.getFresh("result", 1);
                final FunctionSymbol reduce = funSymGen.getFresh("reduce", 1);
                // afterwards the new symbols which depend on f
                final Map<FunctionSymbol, Triple<FunctionSymbol, FunctionSymbol, FunctionSymbol[]>> fMap = new LinkedHashMap<FunctionSymbol, Triple<FunctionSymbol, FunctionSymbol, FunctionSymbol[]>>(
                        sigSize);
                int maxArity = 0;
                for (final FunctionSymbol f : sig) {
                    final int n = f.getArity();
                    if (n > maxArity) {
                        maxArity = n;
                    }
                    final FunctionSymbol g = funSymGen.getFresh("check_"
                            + f.getName(), 1);
                    final FunctionSymbol h = funSymGen.getFresh("redex_"
                            + f.getName(), n);
                    final FunctionSymbol[] is = new FunctionSymbol[n];
                    for (int i = 0; i < n; i++) {
                        is[i] = funSymGen.getFresh("in_" + f.getName() + "_"
                                + (i + 1), n);
                    }
                    fMap
                            .put(
                                    f,
                                    new Triple<FunctionSymbol, FunctionSymbol, FunctionSymbol[]>(
                                            g, h, is));
                }

                // create some variables
                final TRSVariable x = TRSTerm.createVariable("x");
                final TRSVariable[] xs = new TRSVariable[maxArity];
                for (int i = 0; i < maxArity; i++) {
                    xs[i] = TRSTerm.createVariable("x_" + (i + 1));
                }

                // create the rules
                final Set<Rule> newRules = new LinkedHashSet<Rule>(1 + 2
                        * sigSize + R.size() + 2 * sigSize * 2);

                // top(goup(x)) -> top(reduce(x))
                newRules.add(Rule.create(TRSTerm.createFunctionApplication(top,
                        new TRSTerm[] { TRSTerm.createFunctionApplication(goup,
                                new TRSTerm[] { x }) }), TRSTerm
                        .createFunctionApplication(top, new TRSTerm[] { TRSTerm
                                .createFunctionApplication(reduce,
                                        new TRSTerm[] { x }) })));

                // reduce(f(x1,...)) -> checkf(redexf(x1,..))
                for (final FunctionSymbol f : sig) {
                    final int n = f.getArity();
                    final TRSTerm[] args = new TRSTerm[n];
                    for (int i = 0; i < n; i++) {
                        args[i] = xs[i];
                    }
                    final Triple<FunctionSymbol, FunctionSymbol, FunctionSymbol[]> chReIn = fMap
                            .get(f);
                    newRules.add(Rule.create(TRSTerm.createFunctionApplication(
                            reduce, new TRSTerm[] { TRSTerm
                                    .createFunctionApplication(f, args) }),
                            TRSTerm.createFunctionApplication(chReIn.x,
                                    new TRSTerm[] { TRSTerm
                                            .createFunctionApplication(
                                                    chReIn.y, args) })));
                }

                // redexf(l1,...) -> result(r)
                for (final Rule rule : R) {
                    final TRSFunctionApplication left = rule.getLeft();
                    final FunctionSymbol f = left.getRootSymbol();
                    newRules.add(Rule.create(TRSTerm.createFunctionApplication(
                            fMap.get(f).y, left.getArguments()), TRSTerm
                            .createFunctionApplication(result,
                                    new TRSTerm[] { rule.getRight() })));
                }

                // checkf(result(x)) -> goup(x)
                for (final FunctionSymbol f : sig) {
                    final Triple<FunctionSymbol, FunctionSymbol, FunctionSymbol[]> chReIn = fMap
                            .get(f);
                    newRules
                            .add(Rule.create(TRSTerm.createFunctionApplication(
                                    chReIn.x, new TRSTerm[] { TRSTerm
                                            .createFunctionApplication(result,
                                                    new TRSTerm[] { x }) }), TRSTerm
                                    .createFunctionApplication(goup,
                                            new TRSTerm[] { x })));
                }

                // checkf(redexf(x1,...)) -> in_fi(x1,..,reduce(xi),..)
                for (final FunctionSymbol f : sig) {
                    final int n = f.getArity();
                    final TRSTerm[] args = new TRSTerm[n];
                    for (int i = 0; i < n; i++) {
                        args[i] = xs[i];
                    }
                    final Triple<FunctionSymbol, FunctionSymbol, FunctionSymbol[]> chReIn = fMap
                            .get(f);
                    final FunctionSymbol ch = chReIn.x;
                    final FunctionSymbol re = chReIn.y;
                    final FunctionSymbol[] ins = chReIn.z;
                    for (int i = 0; i < n; i++) {
                        final TRSFunctionApplication l = TRSTerm
                                .createFunctionApplication(ch,
                                        new TRSTerm[] { TRSTerm
                                                .createFunctionApplication(re,
                                                        args) });
                        final TRSVariable xi = xs[i];
                        if (Globals.useAssertions) {
                            assert (xi.equals(args[i]));
                        }
                        args[i] = TRSTerm.createFunctionApplication(reduce,
                                new TRSTerm[] { xi });
                        final TRSTerm r = TRSTerm.createFunctionApplication(ins[i],
                                args);
                        args[i] = xi;
                        newRules.add(Rule.create(l, r));
                    }
                }

                // in_fi(x1,...,goup(xi),...) -> goup(f(x1,...))
                for (final FunctionSymbol f : sig) {
                    final int n = f.getArity();
                    final TRSTerm[] args = new TRSTerm[n];
                    for (int i = 0; i < n; i++) {
                        args[i] = xs[i];
                    }
                    final FunctionSymbol[] ins = fMap.get(f).z;
                    for (int i = 0; i < n; i++) {
                        final TRSTerm r = TRSTerm.createFunctionApplication(goup,
                                new TRSTerm[] { TRSTerm.createFunctionApplication(f,
                                        args) });
                        final TRSVariable xi = xs[i];
                        if (Globals.useAssertions) {
                            assert (xi.equals(args[i]));
                        }
                        args[i] = TRSTerm.createFunctionApplication(goup,
                                new TRSTerm[] { xi });
                        final TRSFunctionApplication l = TRSTerm
                                .createFunctionApplication(ins[i], args);
                        args[i] = xi;
                        newRules.add(Rule.create(l, r));
                    }
                }

                final boolean innermost = true;
                return new Quadruple<Set<Rule>, Boolean, YNMImplication, QTRSProof>(
                        newRules, innermost, YNMImplication.EQUIVALENT,
                        new TransformationProof(newRules, this, innermost));
            }

            @Override
            public boolean isApplicable(final OTRSProblem otrs) {
                return true;
            }

        },

        /**
         * the thiemann-transformation where constructions and constants are treated specially
         * (shortcut-rules)
         */
        ThiemannII {
            @Override
            public String toString() {
                return "Thiemann-SpecialC";
            }

            @Override
            public String cite(final Export_Util eu) {
                return ""; // TODO publish a paper :-)
            }

            @Override
            public Quadruple<Set<Rule>, Boolean, YNMImplication, QTRSProof> getTransformed(
                    final Set<Rule> R, final Set<FunctionSymbol> sig) {
                final int sigSize = sig.size();
                final int roughlyNewSize = 3 * sigSize + 4 + sigSize * 2; // the last 2 is considered to be the average arity for the in_f_i's
                final FunctionSymbolGenerator funSymGen = new FunctionSymbolGenerator(
                        roughlyNewSize);
                final Set<FunctionSymbol> C = new LinkedHashSet<FunctionSymbol>(
                        sigSize);
                C.addAll(sig);
                final Set<FunctionSymbol> D = new LinkedHashSet<FunctionSymbol>(
                        sigSize);
                for (final Rule rule : R) {
                    final FunctionSymbol f = rule.getRootSymbol();
                    C.remove(f);
                    D.add(f);
                }
                // first copy the original signature
                for (final FunctionSymbol f : sig) {
                    final FunctionSymbol g = funSymGen.getFresh(f.getName(), f
                            .getArity());
                    if (Globals.useAssertions) {
                        assert (f.equals(g));
                    }
                }
                // then create the new unique symbols
                final FunctionSymbol top = funSymGen.getFresh("top", 1);
                final FunctionSymbol goup = funSymGen.getFresh("go_up", 1);
                final FunctionSymbol reduce = funSymGen.getFresh("reduce", 1);
                // afterwards the new symbols which depend on f
                final Map<FunctionSymbol, Triple<FunctionSymbol, FunctionSymbol, FunctionSymbol[]>> fMap = new LinkedHashMap<FunctionSymbol, Triple<FunctionSymbol, FunctionSymbol, FunctionSymbol[]>>(
                        sigSize);
                int maxArity = 0;
                for (final FunctionSymbol f : sig) {
                    final int n = f.getArity();
                    if (n > maxArity) {
                        maxArity = n;
                    }
                    final FunctionSymbol g = funSymGen.getFresh("check_"
                            + f.getName(), 1);
                    final FunctionSymbol h = funSymGen.getFresh("redex_"
                            + f.getName(), n);
                    final FunctionSymbol[] is = new FunctionSymbol[n + 1];
                    for (int i = 0; i < n; i++) {
                        is[i] = funSymGen.getFresh("in_" + f.getName() + "_"
                                + (i + 1), n);
                    }
                    is[n] = funSymGen.getFresh("result_" + f.getName(), 1);

                    fMap
                            .put(
                                    f,
                                    new Triple<FunctionSymbol, FunctionSymbol, FunctionSymbol[]>(
                                            g, h, is));
                }

                // create some variables
                final TRSVariable x = TRSTerm.createVariable("x");
                final TRSVariable[] xs = new TRSVariable[maxArity];
                for (int i = 0; i < maxArity; i++) {
                    xs[i] = TRSTerm.createVariable("x_" + (i + 1));
                }

                // create the rules
                final Set<Rule> newRules = new LinkedHashSet<Rule>(1 + 2
                        * sigSize + R.size() + 2 * sigSize * 2);

                // top(goup(x)) -> top(reduce(x))
                newRules.add(Rule.create(TRSTerm.createFunctionApplication(top,
                        new TRSTerm[] { TRSTerm.createFunctionApplication(goup,
                                new TRSTerm[] { x }) }), TRSTerm
                        .createFunctionApplication(top, new TRSTerm[] { TRSTerm
                                .createFunctionApplication(reduce,
                                        new TRSTerm[] { x }) })));

                // reduce(f(x1,...)) -> checkf(redexf(x1,..)) for defined symbols but no constants
                for (final FunctionSymbol f : D) {
                    final int n = f.getArity();
                    if (n == 0) {
                        continue;
                    }
                    final TRSTerm[] args = new TRSTerm[n];
                    for (int i = 0; i < n; i++) {
                        args[i] = xs[i];
                    }
                    final Triple<FunctionSymbol, FunctionSymbol, FunctionSymbol[]> chReIn = fMap
                            .get(f);
                    newRules.add(Rule.create(TRSTerm.createFunctionApplication(
                            reduce, new TRSTerm[] { TRSTerm
                                    .createFunctionApplication(f, args) }),
                            TRSTerm.createFunctionApplication(chReIn.x,
                                    new TRSTerm[] { TRSTerm
                                            .createFunctionApplication(
                                                    chReIn.y, args) })));
                }

                // redexf(l1,...) -> resultf(r) for n > 0 or reduce(l) -> goup(r) if l is a constant
                for (final Rule rule : R) {
                    final TRSFunctionApplication left = rule.getLeft();
                    final FunctionSymbol f = left.getRootSymbol();
                    if (f.getArity() > 0) {
                        final FunctionSymbol[] fs = fMap.get(f).z;
                        final FunctionSymbol resultf = fs[fs.length - 1];
                        newRules.add(Rule.create(TRSTerm
                                .createFunctionApplication(fMap.get(f).y, left
                                        .getArguments()), TRSTerm
                                .createFunctionApplication(resultf,
                                        new TRSTerm[] { rule.getRight() })));
                    } else {
                        newRules.add(Rule.create(TRSTerm
                                .createFunctionApplication(reduce,
                                        new TRSTerm[] { left }), TRSTerm
                                .createFunctionApplication(goup,
                                        new TRSTerm[] { rule.getRight() })));
                    }
                }

                // checkf(result(x)) -> goup(x) for defined symbols of arity > 0
                for (final FunctionSymbol f : D) {
                    if (f.getArity() == 0) {
                        continue;
                    }
                    final Triple<FunctionSymbol, FunctionSymbol, FunctionSymbol[]> chReIn = fMap
                            .get(f);
                    final FunctionSymbol resultf = chReIn.z[chReIn.z.length - 1];
                    newRules
                            .add(Rule.create(TRSTerm.createFunctionApplication(
                                    chReIn.x, new TRSTerm[] { TRSTerm
                                            .createFunctionApplication(resultf,
                                                    new TRSTerm[] { x }) }), TRSTerm
                                    .createFunctionApplication(goup,
                                            new TRSTerm[] { x })));
                }

                // checkf(redexf(x1,...)) -> in_fi(x1,..,reduce(xi),..) for defined symbols
                for (final FunctionSymbol f : D) {
                    final int n = f.getArity();
                    final TRSTerm[] args = new TRSTerm[n];
                    for (int i = 0; i < n; i++) {
                        args[i] = xs[i];
                    }
                    final Triple<FunctionSymbol, FunctionSymbol, FunctionSymbol[]> chReIn = fMap
                            .get(f);
                    final FunctionSymbol ch = chReIn.x;
                    final FunctionSymbol re = chReIn.y;
                    final FunctionSymbol[] ins = chReIn.z;
                    for (int i = 0; i < n; i++) {
                        final TRSFunctionApplication l = TRSTerm
                                .createFunctionApplication(ch,
                                        new TRSTerm[] { TRSTerm
                                                .createFunctionApplication(re,
                                                        args) });
                        final TRSVariable xi = xs[i];
                        if (Globals.useAssertions) {
                            assert (xi.equals(args[i]));
                        }
                        args[i] = TRSTerm.createFunctionApplication(reduce,
                                new TRSTerm[] { xi });
                        final TRSTerm r = TRSTerm.createFunctionApplication(ins[i],
                                args);
                        args[i] = xi;
                        newRules.add(Rule.create(l, r));
                    }
                }

                // reduce(f(x1,...)) -> in_fi(x1,..,reduce(xi),..) for constructors
                for (final FunctionSymbol f : C) {
                    final int n = f.getArity();
                    final TRSTerm[] args = new TRSTerm[n];
                    for (int i = 0; i < n; i++) {
                        args[i] = xs[i];
                    }
                    final FunctionSymbol[] ins = fMap.get(f).z;
                    for (int i = 0; i < n; i++) {
                        final TRSFunctionApplication l = TRSTerm
                                .createFunctionApplication(reduce,
                                        new TRSTerm[] { TRSTerm
                                                .createFunctionApplication(f,
                                                        args) });
                        final TRSVariable xi = xs[i];
                        if (Globals.useAssertions) {
                            assert (xi.equals(args[i]));
                        }
                        args[i] = TRSTerm.createFunctionApplication(reduce,
                                new TRSTerm[] { xi });
                        final TRSTerm r = TRSTerm.createFunctionApplication(ins[i],
                                args);
                        args[i] = xi;
                        newRules.add(Rule.create(l, r));
                    }
                }

                // in_fi(x1,...,goup(xi),...) -> goup(f(x1,...))
                for (final FunctionSymbol f : sig) {
                    final int n = f.getArity();
                    final TRSTerm[] args = new TRSTerm[n];
                    for (int i = 0; i < n; i++) {
                        args[i] = xs[i];
                    }
                    final FunctionSymbol[] ins = fMap.get(f).z;
                    for (int i = 0; i < n; i++) {
                        final TRSTerm r = TRSTerm.createFunctionApplication(goup,
                                new TRSTerm[] { TRSTerm.createFunctionApplication(f,
                                        args) });
                        final TRSVariable xi = xs[i];
                        if (Globals.useAssertions) {
                            assert (xi.equals(args[i]));
                        }
                        args[i] = TRSTerm.createFunctionApplication(goup,
                                new TRSTerm[] { xi });
                        final TRSFunctionApplication l = TRSTerm
                                .createFunctionApplication(ins[i], args);
                        args[i] = xi;
                        newRules.add(Rule.create(l, r));
                    }
                }

                final boolean innermost = true;
                return new Quadruple<Set<Rule>, Boolean, YNMImplication, QTRSProof>(
                        newRules, innermost, YNMImplication.EQUIVALENT,
                        new TransformationProof(newRules, this, innermost));
            }

            @Override
            public boolean isApplicable(final OTRSProblem otrs) {
                return true;
            }

        },

        /**
         * the Raffelsieper-Zantema-transformation
         */
        RaffelsieperZantema {
            final boolean enableFlatSymbols = true;
            final boolean enableBlocking = true;

            @Override
            public String toString() {
                return "Raffelsieper-Zantema";
            }

            @Override
            public String cite(final Export_Util eu) {
                return ""; // TODO cite WRS08
            }

            @Override
            public Quadruple<Set<Rule>, Boolean, YNMImplication, QTRSProof> getTransformed(
                    final Set<Rule> R, final Set<FunctionSymbol> sig) {
                final Set<TRSFunctionApplication> lhss = CollectionUtils
                        .getLeftHandSides(R);
                // extend signature by fresh constant to have outermost termination (instead of outermost ground termination)
                String name = "fresh_constan";
                do {
                    name += "t";

                } while (!sig.add(FunctionSymbol.create(name, 0)));

                final Collection<TRSFunctionApplication> SL = Transformation.computeSL(sig, lhss);

                final int sigSize = sig.size();
                final int newSize = 2 * sigSize + 3; // the last 2 is considered to be the average arity for the in_f_i's
                final FunctionSymbolGenerator funSymGen = new FunctionSymbolGenerator(
                        newSize);
                // first copy the original signature
                for (final FunctionSymbol f : sig) {
                    final FunctionSymbol g = funSymGen.getFresh(f.getName(), f
                            .getArity());
                    if (Globals.useAssertions) {
                        assert (f.equals(g));
                    }
                }
                // then create the new unique symbols
                final FunctionSymbol top = funSymGen.getFresh("top", 1);
                final FunctionSymbol up = funSymGen.getFresh("up", 1);
                final FunctionSymbol down = funSymGen.getFresh("down", 1);
                final FunctionSymbol block = funSymGen.getFresh("block", 1);
                // afterwards the new symbols which depend on f
                final Map<FunctionSymbol, FunctionSymbol> fMap = new LinkedHashMap<FunctionSymbol, FunctionSymbol>(
                        sigSize);
                int maxArity = 0;
                for (final FunctionSymbol f : sig) {
                    final int n = f.getArity();
                    if (n > maxArity) {
                        maxArity = n;
                    }
                    fMap.put(f, this.enableFlatSymbols ? funSymGen.getFresh(f
                            .getName()
                            + "_flat", n) : f);
                }

                // create some variables
                final TRSVariable x = TRSTerm.createVariable("x");
                final TRSVariable[] xs = new TRSVariable[maxArity];
                for (int i = 0; i < maxArity; i++) {
                    xs[i] = TRSTerm.createVariable("x_" + (i + 1));
                }

                // create the rules
                final Set<Rule> newRules = new LinkedHashSet<Rule>();

                // down(l) -> up(r)
                for (final Rule rule : R) {
                    final TRSFunctionApplication left = rule.getLeft();
                    final FunctionSymbol f = left.getRootSymbol();
                    newRules.add(Rule.create(TRSTerm.createFunctionApplication(
                            down, new TRSTerm[] { left }), TRSTerm
                            .createFunctionApplication(up, new TRSTerm[] { rule
                                    .getRight() })));
                }

                // top(up(x)) -> top(down(x))
                newRules.add(Rule.create(TRSTerm.createFunctionApplication(top,
                        new TRSTerm[] { TRSTerm.createFunctionApplication(up,
                                new TRSTerm[] { x }) }), TRSTerm
                        .createFunctionApplication(top, new TRSTerm[] { TRSTerm
                                .createFunctionApplication(down,
                                        new TRSTerm[] { x }) })));

                // down(f(t_1,..,t_n)) -> f(block(t_1),..,down(t_i),..) for f(t1,..,tn) in SL
                for (final TRSFunctionApplication ft : SL) {
                    final FunctionSymbol f = ft.getRootSymbol();
                    final List<? extends TRSTerm> ts = ft.getArguments();
                    final int n = f.getArity();
                    final TRSTerm[] args = new TRSTerm[n];
                    for (int i = 0; i < n; i++) {
                        args[i] = this.block(block, ts.get(i));
                    }
                    final FunctionSymbol flatF = fMap.get(f);
                    final TRSFunctionApplication newLeft = TRSTerm
                            .createFunctionApplication(down, new TRSTerm[] { ft });
                    for (int i = 0; i < n; i++) {
                        final TRSTerm old = args[i];
                        args[i] = TRSTerm.createFunctionApplication(down,
                                new TRSTerm[] { ts.get(i) });
                        final TRSTerm r = TRSTerm.createFunctionApplication(flatF,
                                args);
                        newRules.add(Rule.create(newLeft, r));
                        args[i] = old;
                    }
                }

                // fFlat(block(x1),...,up(xi),...) -> up(f(x1,...))
                for (final FunctionSymbol f : sig) {
                    final int n = f.getArity();
                    final TRSTerm[] args = new TRSTerm[n];
                    for (int i = 0; i < n; i++) {
                        args[i] = xs[i];
                    }
                    final TRSTerm right = TRSTerm.createFunctionApplication(up,
                            new TRSTerm[] { TRSTerm
                                    .createFunctionApplication(f, args) });
                    for (int i = 0; i < n; i++) {
                        args[i] = this.block(block, args[i]);
                    }
                    final FunctionSymbol fFlat = fMap.get(f);
                    for (int i = 0; i < n; i++) {
                        final TRSTerm old = args[i];
                        args[i] = TRSTerm.createFunctionApplication(up,
                                new TRSTerm[] { xs[i] });
                        final TRSFunctionApplication l = TRSTerm
                                .createFunctionApplication(fFlat, args);
                        newRules.add(Rule.create(l, right));
                        args[i] = old;
                    }
                }

                final boolean innermost = false;
                return new Quadruple<Set<Rule>, Boolean, YNMImplication, QTRSProof>(
                        newRules, innermost, YNMImplication.SOUND,
                        new TransformationProof(newRules, this, innermost));
            }

            private TRSTerm block(final FunctionSymbol block, final TRSTerm t) {
                if (this.enableBlocking) {
                    return TRSTerm.createFunctionApplication(block,
                            new TRSTerm[] { t });
                } else {
                    return t;
                }
            }

            @Override
            public boolean isApplicable(final OTRSProblem otrs) {
                // check for quasi-left-linearity

                // changed by Sebastian Weise (GeneralizedRules !)
                // we continue only if there are no "real" Generalized Rules in otrs !
                final Set<Rule> simpleRules = new LinkedHashSet<Rule>();
                for (final GeneralizedRule actGeneralizedRule : otrs.getR()) {
                    if (actGeneralizedRule instanceof Rule) {
                        simpleRules.add((Rule) actGeneralizedRule);
                    } else {
                        assert (false);
                        return false;
                    }
                }
                final Set<Rule> R = ImmutableCreator.create(simpleRules);

                ruleLoop: for (final Rule rule : R) {
                    final TRSFunctionApplication l = rule.getLeft();
                    if (!l.isLinear()) {
                        final FunctionSymbol f = l.getRootSymbol();
                        for (final Rule other : R) {
                            final TRSFunctionApplication otherL = other.getLeft();
                            if (otherL.getRootSymbol().equals(f)
                                    && otherL.isLinear() && otherL.matches(l)) {
                                continue ruleLoop;
                            }
                        }
                        return false;
                    }
                }
                return true;
            }
        };

        private static TRSVariable createVar(final Wrapper<Integer> n) {
            final TRSVariable res = TRSTerm
                    .createVariable(TRSTerm.SECOND_STANDARD_PREFIX + n.x);
            n.x++;
            return res;
        }

        /**
         * creates the term f(x_n,...x_{n+i}) and changes n to n+i.
         * @param f
         * @param n
         */
        private static TRSFunctionApplication create(final FunctionSymbol f,
                final Wrapper<Integer> n) {
            int m = n.x;
            final int ar = f.getArity();
            final int newM = ar + m;
            final ArrayList<TRSTerm> args = new ArrayList<TRSTerm>(ar);
            for (; m < newM; m++) {
                args.add(TRSTerm.createVariable(TRSTerm.SECOND_STANDARD_PREFIX + m));
            }
            n.x = newM;
            return TRSTerm.createFunctionApplication(f, ImmutableCreator
                    .create(args));
        }

        /**
         * computes the set S_L in the following way:
         * generate linear terms starting from small ones up to maxDepth
         * Whenever t does not unify with lhs then do not generate further instances
         * Whenever t is matched by some lhs then stop since all further instances will be matched.
         * Otherwise, expand all possibilities at given depth: take all variables at depth n and then replace expand them or not
         * @param sig
         * @param lhss will be modified
         * @return
         */
        private static Collection<TRSFunctionApplication> computeSL(
                final Set<FunctionSymbol> sig,
                final Set<TRSFunctionApplication> lhss) {
            final Iterator<TRSFunctionApplication> lhsIt = lhss.iterator();
            int maxDepth = 0;
            while (lhsIt.hasNext()) {
                // only consider linear lhss since the non-linear ones are already
                // matched by other linear terms. (see isApplicable)
                final TRSTerm l = lhsIt.next();
                if (l.isLinear()) {
                    final int d = l.getDepthConstant();
                    if (d > maxDepth) {
                        maxDepth = d;
                    }
                } else {
                    lhsIt.remove();
                }
            }
            // construct a quick lookup map to get possible lhss
            final Map<FunctionSymbol, Collection<TRSFunctionApplication>> fToLhs = Transformation.createLhsMap(
                    lhss, true);

            // set of considered terms
            Collection<TRSFunctionApplication> todo = new ArrayList<TRSFunctionApplication>();
            Collection<TRSFunctionApplication> newTodo = new ArrayList<TRSFunctionApplication>();
            final Collection<TRSFunctionApplication> SL = new ArrayList<TRSFunctionApplication>();

            // generate the initial todos
            final Wrapper<Integer> varNum = new Wrapper<Integer>(0);
            int level = 1;
            for (final FunctionSymbol f : sig) {
                if (fToLhs.containsKey(f)) {
                    // defined symbol
                    todo.add(Transformation.create(f, varNum));
                } else {
                    SL.add(Transformation.create(f, varNum));
                }
            }

            // put the signature into an array
            final int sigSize = sig.size();
            final FunctionSymbol[] sigArr = new FunctionSymbol[sigSize];
            int j = 0;
            for (final FunctionSymbol f : sig) {
                sigArr[j] = f;
                j++;
            }

            while (!todo.isEmpty()) {
                final boolean maxLevel = level == maxDepth;

                newTodo.clear();
                tLoop: for (final TRSFunctionApplication t : todo) {
                    final FunctionSymbol f = t.getRootSymbol();
                    final Collection<TRSFunctionApplication> possLhs = fToLhs
                            .get(f);
                    for (final TRSFunctionApplication lhs : possLhs) {
                        if (lhs.matches(t)) { // if a match is detected then all
                            // instances of t won't belong to SL
                            continue tLoop;
                        }
                    }
                    boolean unifies = false;
                    for (final TRSFunctionApplication lhs : possLhs) {
                        if (lhs.unifies(t)) { // no variable renaming since lhs has only STANDARD_PREFIX whereas
                            // t starts with SECOND_STANDARD_PREFIX
                            unifies = true;
                            break;
                        }
                    }
                    if (!unifies) {
                        // t will be inserted and all further instances will also be inserted
                        SL.add(t);
                        continue;
                    }

                    if (maxLevel) {
                        continue;
                    }

                    // we have to expand t in all possible ways at variable positions of current level
                    final Map<TRSVariable, List<Position>> varList = t
                            .getVariablePositions();
                    final Iterator<List<Position>> i = varList.values()
                            .iterator();
                    while (i.hasNext()) {
                        final List<Position> ps = i.next();
                        if (Globals.useAssertions) {
                            assert (ps.size() == 1);
                        }
                        final Position p = ps.get(0);
                        if (p.getDepth() != level) {
                            i.remove();
                        }
                    }

                    // now let us take all instances
                    final int numVars = varList.size();
                    final Iterator<int[]> iter = new VectorEnumerator(numVars,
                            sigSize).iterator();
                    while (iter.hasNext()) {
                        int k = 0;
                        final int[] replacement = iter.next();
                        boolean oneNonVar = false;
                        TRSFunctionApplication newTerm = t;
                        for (final List<Position> ps : varList.values()) {
                            final int num = replacement[k];
                            k++;
                            TRSTerm subTerm;
                            if (num == 0) {
                                subTerm = Transformation.createVar(varNum);
                            } else {
                                oneNonVar = true;
                                final FunctionSymbol g = sigArr[num - 1];
                                subTerm = Transformation.create(g, varNum);
                            }
                            newTerm = (TRSFunctionApplication) newTerm.replaceAt(
                                    ps.get(0), subTerm);
                        }
                        if (oneNonVar) {
                            newTodo.add(newTerm);
                        }
                    }
                }

                level++;
                final Collection<TRSFunctionApplication> tmp = newTodo;
                newTodo = todo;
                todo = tmp;
            }

            // okay, now we are nearly done, it only remains to remove instances
            final Map<FunctionSymbol, Collection<TRSFunctionApplication>> SLmap = Transformation.createLhsMap(
                    SL, false);
            final Iterator<TRSFunctionApplication> slIter = SL.iterator();
            while (slIter.hasNext()) {
                final TRSFunctionApplication slTerm = slIter.next();
                if (slTerm.getRootSymbol().getArity() == 0) {
                    slIter.remove();
                    continue;
                }
                final Collection<TRSFunctionApplication> others = SLmap.get(slTerm
                        .getRootSymbol());
                for (final TRSFunctionApplication other : others) {
                    if (!slTerm.equals(other)) {
                        if (other.matches(slTerm)) {
                            // slTerm is not needed!
                            slIter.remove();
                            others.remove(slTerm);
                            break;
                        }
                    }
                }
            }

            return SL;

        }

        /**
         * returns a lookup map from function symbols to corresponding lhss
         * @param variableRenaming if true then it is additionally ensured that all lhss in the returned map only use the STANDARD VARIABLE PREFIX.
         *                 if false then terms are not variable renamed
         * @param lhss
         * @return
         */
        private static Map<FunctionSymbol, Collection<TRSFunctionApplication>> createLhsMap(
                final Iterable<TRSFunctionApplication> lhss,
                final boolean variableRenaming) {
            final Map<FunctionSymbol, Collection<TRSFunctionApplication>> fToLhs = new HashMap<FunctionSymbol, Collection<TRSFunctionApplication>>();
            for (final TRSFunctionApplication t : lhss) {
                final FunctionSymbol f = t.getRootSymbol();
                Collection<TRSFunctionApplication> ts = fToLhs.get(f);
                if (ts == null) {
                    ts = new ArrayList<TRSFunctionApplication>();
                    fToLhs.put(f, ts);
                }
                ts.add(variableRenaming ? (TRSFunctionApplication) t
                        .getStandardRenumbered() : t);
            }
            return fToLhs;
        }

        public abstract String cite(Export_Util eu);

        /**
         * Transforms an outermost TRS to a standard TRS.
         * returns the transformed set of rules,
         * whether we should use innermost afterwards,
         * the implication and the proof.
         * @param R
         * @param signature
         * @return
         */
        public abstract Quadruple<Set<Rule>, Boolean, YNMImplication, QTRSProof> getTransformed(
                Set<Rule> R, Set<FunctionSymbol> signature);

        public abstract boolean isApplicable(OTRSProblem otrs);
    };

    private static final class TransformationProof extends QTRSProof {

        private final Transformation transformation;
        private final boolean innermost;

        public TransformationProof(final Set<Rule> rules,
                final Transformation transformation, final boolean innermost) {
            final String name = transformation.toString() + "-Transformation";
            this.longName = name;
            this.shortName = name;
            this.transformation = transformation;
            this.innermost = innermost;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "We applied the " + this.transformation + " transformation "
                    + this.transformation.cite(o)
                    + " to transform the outermost TRS to a"
                    + (this.innermost ? "n innermost" : " standard") + " TRS.";
        }

    }

    /**
     * very simple fresh name generator
     */
    private static final class FunctionSymbolGenerator {

        private final Set<FunctionSymbol> fs;

        public FunctionSymbolGenerator(final int size) {
            this.fs = new HashSet<FunctionSymbol>(size);
        }

        public FunctionSymbol getFresh(final String name, final int arity) {
            int j = 0;
            String currentName = name;
            FunctionSymbol f;
            while (true) {
                f = FunctionSymbol.create(currentName, arity);
                if (this.fs.add(f)) {
                    return f;
                } else {
                    currentName = name + j;
                    j++;
                }
            }
        }

    }

    public static class Arguments {
        public Transformation transformation = Transformation.Thiemann;
    }
}
