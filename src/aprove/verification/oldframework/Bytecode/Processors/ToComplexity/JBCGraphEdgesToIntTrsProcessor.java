package aprove.verification.oldframework.Bytecode.Processors.ToComplexity;

import static aprove.verification.oldframework.IntTRS.PoloRedPair.ToolBox.*;
import static aprove.verification.oldframework.Utility.Collection_Util.*;
import static java.util.Collections.*;
import static java.util.stream.Collectors.*;

import java.math.*;
import java.util.*;
import java.util.Map.*;
import java.util.function.*;
import java.util.stream.*;

import aprove.input.Programs.jbc.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.dpframework.JBCProblem.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Bytecode.JBCOptions.*;
import aprove.verification.oldframework.Bytecode.Merger.StatePosition.*;
import aprove.verification.oldframework.Bytecode.OpCodes.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.Processors.ToSCC.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.ClassInitializationInformation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.InputReferenceChangeInformation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.InputReferenceChangeInformation.IrChangeInformation.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.CostEquationSystem.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.WeightedIntTrs.*;
import immutables.*;

public class JBCGraphEdgesToIntTrsProcessor extends Processor.ProcessorSkeleton {

    public static final TRSVariable ENV = TRSTerm.createVariable("env");
    public static final TRSVariable STATIC = TRSTerm.createVariable("static");
    public static final TRSVariable RET = TRSTerm.createVariable("ret");
    public static final TRSVariable EXC = TRSTerm.createVariable("exc");

    protected final Arguments args;

    public static enum TargetSystem {
        IntTrs("a weighted ITS"),
        IRS("an ITS"),
        CES("a CES");

        String text;
        private TargetSystem(String text) {
            this.text = text;
        }

    }

    public static class Arguments {
        public boolean simpleDivModEncoding = true;
        public TargetSystem targetSystem = TargetSystem.IntTrs;
        public boolean filterUnneededConditions = true;
        // blows up the ITS, so you usually don't want to do that
        public boolean computeTransitiveClosureOfRelevantConditions = false;
        public boolean filterFieldsOfTypeObject = false;
        public boolean lowerBoundsForWriteAccesses = false;
        public boolean preciseTreeEncoding = true;

        /*
         * Currently, there is a bug in CoFloCo that requires us to always generate these edges.
         * If they are not generated, some nonterminating examples will be falsely proven as termining.
         * However, generating these rules makes cofloco unable to prove the complexity of examples that are more complex then linear.
         * A workaround is to not generate the rules and combine the results with the termination backend of aprove to remove false positives.
         */
        public boolean alwaysGenerateCallEdges = true;

        public static StaticOption<Boolean> cliPropagateLowerBounds = new StaticOption<>();
        private InstanceOption<Boolean> propagateLowerBounds = new InstanceOption<>(false, cliPropagateLowerBounds);

        public boolean propagateLowerBounds() {
            return propagateLowerBounds.get();
        }

        public void setPropagateLowerBounds(boolean b) {
            propagateLowerBounds.set(b);
        }

    }

    private static Map<String, String> forbiddenSubStrings = new LinkedHashMap<>();

    static {
        forbiddenSubStrings.put("-", "NEG");
        forbiddenSubStrings.put("#", "NULL");
        forbiddenSubStrings.put("$", "DOLLAR");
    }

    final Condition True = new ConjunctiveClause(emptySet()).asCondition();

    private enum Sign {
        Negative, NonNegative, Unknown
    }

    private static class Literal {
        TRSFunctionApplication f;

        Literal(TRSFunctionApplication f) {
            this.f = f;
        }

        static Literal eq(TRSTerm x, TRSTerm y) {
            return new Literal(buildEq(x, y));
        }

        static Literal neq(TRSTerm x, TRSTerm y) {
            return new Literal(buildNot(buildEq(x, y)));
        }

        static Literal lt(TRSTerm s, TRSTerm t) {
            return new Literal(buildLt(s, t));
        }

        static Literal positive(TRSTerm t) {
            return new Literal(buildPositive(t));
        }

        static Literal nonPositive(TRSTerm t) {
            return new Literal(buildNonPositive(t));
        }

        static Literal le(TRSTerm s, TRSTerm t) {
            return new Literal(buildLe(s, t));
        }

        static Literal nonNegative(TRSTerm t) {
            return new Literal(buildNonNegative(t));
        }

        Literal applySubstitution(TRSSubstitution sigma) {
            return new Literal(f.applySubstitution(sigma));
        }

        @Override
        public String toString() {
            return f.toString();
        }

        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result + ((f == null) ? 0 : f.hashCode());
            return result;
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj)
                return true;
            if (obj == null)
                return false;
            if (getClass() != obj.getClass())
                return false;
            Literal other = (Literal) obj;
            if (f == null) {
                if (other.f != null)
                    return false;
            } else if (!f.equals(other.f))
                return false;
            return true;
        }

        public Set<TRSVariable> getVariables() {
            return f.getVariables();
        }

    }

    private class ConjunctiveClause {

        Set<Literal> literals;

        ConjunctiveClause(Set<Literal> literals) {
            this.literals = literals;
        }

        ConjunctiveClause(Literal l) {
            this(singleton(l));
        }

        ConjunctiveClause and(ConjunctiveClause that) {
            return new ConjunctiveClause(union(this.literals, that.literals));
        }

        ConjunctiveClause and(Literal l) {
            return and(new ConjunctiveClause(l));
        }

        Condition or(ConjunctiveClause that) {
            Set<ConjunctiveClause> dnf = new LinkedHashSet<>();
            dnf.add(this);
            dnf.add(that);
            return new Condition(dnf);
        }

        TRSTerm asTerm() {
            return buildAnd(literals.stream().map(x -> x.f).collect(toSet()));
        }

        Condition asCondition() {
            return new Condition(this);
        }

        ConjunctiveClause applySubstitution(TRSSubstitution sigma) {
            return new ConjunctiveClause(literals.stream().map(c -> c.applySubstitution(sigma)).collect(toSet()));
        }

        @Override
        public String toString() {
            return literals.stream().reduce("true", (x, y) -> y + " /\\ " + x, (x, y) -> y + x);
        }

        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result + ((literals == null) ? 0 : literals.hashCode());
            return result;
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj)
                return true;
            if (obj == null)
                return false;
            if (getClass() != obj.getClass())
                return false;
            ConjunctiveClause other = (ConjunctiveClause) obj;
            if (literals == null) {
                if (other.literals != null)
                    return false;
            } else if (!literals.equals(other.literals))
                return false;
            return true;
        }

        public ConjunctiveClause filterUnneededConditions(Set<TRSVariable> relevantVars) {
            return new ConjunctiveClause(literals.stream().filter(x -> relevantVars.containsAll(x.getVariables())).collect(toSet()));
        }

        public ConjunctiveClause removeLiteralsFor(TRSVariable var) {
            return new ConjunctiveClause(literals.stream().filter(x -> !x.getVariables().contains(var)).collect(toSet()));
        }

    }

    private class Condition {

        Set<ConjunctiveClause> dnf = new LinkedHashSet<>();

        Condition(Set<ConjunctiveClause> dnf) {
            this.dnf = dnf;
        }

        Condition(ConjunctiveClause c) {
            this(singleton(c));
        }

        Condition(Literal l) {
            this(new ConjunctiveClause(l));
        }

        Stream<ConjunctiveClause> stream() {
            return dnf.stream();
        }

        Condition and(Condition that) {
            Set<ConjunctiveClause> newClauses = new LinkedHashSet<>();
            for (ConjunctiveClause fromThis: this.dnf) {
                for (ConjunctiveClause fromThat: that.dnf) {
                    newClauses.add(fromThis.and(fromThat));
                }
            }
            return new Condition(newClauses);
        }

        Condition and(ConjunctiveClause c) {
            return and(new Condition(c));
        }

        Condition and(Literal l) {
            return and(new ConjunctiveClause(l));
        }

        @Override
        public String toString() {
            return dnf.stream().reduce("false", (x, y) -> "(" + y + " \\/ " + x + ")", (x, y) -> y + x);
        }

        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result + ((dnf == null) ? 0 : dnf.hashCode());
            return result;
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj)
                return true;
            if (obj == null)
                return false;
            if (getClass() != obj.getClass())
                return false;
            Condition other = (Condition) obj;
            if (dnf == null) {
                if (other.dnf != null)
                    return false;
            } else if (!dnf.equals(other.dnf))
                return false;
            return true;
        }

        public Condition applySubstitution(Map<TRSVariable, TRSVariable> sigma) {
            TRSSubstitution subst = TRSSubstitution.create(ImmutableCreator.create(sigma));
            return new Condition(dnf.stream().map(x -> x.applySubstitution(subst)).collect(toSet()));
        }

        public Condition filterUnneededConditions(Set<TRSVariable> relevantVars) {
            Set<TRSVariable> allRelevantVars = new LinkedHashSet<>(relevantVars);
            if (args.computeTransitiveClosureOfRelevantConditions) {
                boolean changed;
                do {
                    changed = false;
                    for (ConjunctiveClause x: dnf) {
                        for (Literal l: x.literals) {
                            if (!areDisjoint(l.getVariables(), allRelevantVars)) {
                                changed |= allRelevantVars.addAll(l.getVariables());
                            }
                        }
                    }
                } while (changed);
            }
            return new Condition(dnf.stream().map(x -> x.filterUnneededConditions(allRelevantVars)).collect(toSet()));
        }

        public Condition or(Condition c) {
            Set<ConjunctiveClause> newClauses = new LinkedHashSet<>(dnf);
            newClauses.addAll(c.dnf);
            return new Condition(newClauses);
        }

    }

    protected class Rule {

        TRSFunctionApplication lhs;
        List<TRSFunctionApplication> rhs;
        Condition c;
        SimplePolynomial lowerBound;
        SimplePolynomial upperBound;
        List<TRSTerm> lhsOutputVariables;

        Rule(TRSFunctionApplication lhs, List<TRSFunctionApplication> rhs, Condition c, SimplePolynomial lowerBound, SimplePolynomial upperBound, List<TRSTerm> lhsOutputVariables) {
            this.lhs = lhs;
            this.rhs = rhs;
            this.c = c;
            this.lowerBound = lowerBound;
            this.upperBound = upperBound;
            this.lhsOutputVariables = lhsOutputVariables;
        }

        Rule(TRSFunctionApplication lhs, List<TRSFunctionApplication> rhs, Condition c, SimplePolynomial lowerBound, SimplePolynomial upperBound) {
            this.lhs = lhs;
            this.rhs = rhs;
            this.c = c;
            this.lowerBound = lowerBound;
            this.upperBound = upperBound;
        }

        public Set<WeightedRule> toWeightedRules() {
            if (rhs.size() == 0)
                return Collections.emptySet();
            assert rhs.size() == 1;
            return c.stream().map(x -> new WeightedRule(IGeneralizedRule.create(lhs, rhs.iterator().next(), x.asTerm()), lowerBound, upperBound)).collect(toSet());
        }

        public Set<IGeneralizedRule> toIRSRules() {
            if (rhs.size() == 0)
                return Collections.emptySet();
            assert rhs.size() == 1;
            return c.stream().map(x -> IGeneralizedRule.create(lhs, rhs.iterator().next(), x.asTerm())).collect(toSet());
        }

        public Set<CostEquation> toCostEquation() {
            return c.stream().map(x -> CostEquation.create(lhs, rhs, (TRSFunctionApplication)x.asTerm(), upperBound, lhsOutputVariables)).collect(toSet());
        }

        public Rule filterUnneededConditions() {
            if (args.filterUnneededConditions) {
                return new Rule(lhs, rhs, c.filterUnneededConditions(getVars()), lowerBound, upperBound, lhsOutputVariables);
            } else {
                return this;
            }
        }

        public Set<TRSVariable> getVars() {
            Set<TRSVariable> res = new HashSet<>(lhs.getVariables());
            for (TRSFunctionApplication r : rhs) {
                res.addAll(r.getVariables());
            }
            return res;
        }

        @Override
        public String toString() {
            return lhs + " -> " + rhs + " :|: " + c + ", costs: [" + lowerBound + ", " + upperBound + "]";
        }

        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result + ((c == null) ? 0 : c.hashCode());
            result = prime * result + ((lhs == null) ? 0 : lhs.hashCode());
            result = prime * result + ((lowerBound == null) ? 0 : lowerBound.hashCode());
            result = prime * result + ((rhs == null) ? 0 : rhs.hashCode());
            result = prime * result + ((upperBound == null) ? 0 : upperBound.hashCode());
            return result;
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj)
                return true;
            if (obj == null)
                return false;
            if (getClass() != obj.getClass())
                return false;
            Rule other = (Rule) obj;
            if (c == null) {
                if (other.c != null)
                    return false;
            } else if (!c.equals(other.c))
                return false;
            if (lhs == null) {
                if (other.lhs != null)
                    return false;
            } else if (!lhs.equals(other.lhs))
                return false;
            if (lowerBound == null) {
                if (other.lowerBound != null)
                    return false;
            } else if (!lowerBound.equals(other.lowerBound))
                return false;
            if (rhs == null) {
                if (other.rhs != null)
                    return false;
            } else if (!rhs.equals(other.rhs))
                return false;
            if (upperBound == null) {
                if (other.upperBound != null)
                    return false;
            } else if (!upperBound.equals(other.upperBound))
                return false;
            return true;
        }

    }

    protected class RulesTransformer {

        private class BasicEdgeTransformation {

            BasicNodeTransformation left;
            List<BasicNodeTransformation> right = new ArrayList<>();
            Condition c = new Condition(Literal.eq(createVariable(AbstractVariableReference.NULLREF), ZERO));
            SimplePolynomial lowerBound;
            SimplePolynomial upperBound;

            BasicEdgeTransformation(Edge e) {
                BasicNodeTransformation lhs = new BasicNodeTransformation(e.getStart());
                BasicNodeTransformation rhs = new BasicNodeTransformation(e.getEnd());
                Pair<SimplePolynomial, SimplePolynomial> costs = computeCosts(e);
                this.left = lhs;
                if (!e.getEnd().getState().callStackEmpty())
                    this.right.add(rhs);
                this.lowerBound = costs.x;
                this.upperBound = costs.y;
            }

            private Pair<SimplePolynomial, SimplePolynomial> computeCosts(Edge e) {
                switch(edges.getGoal()) {
                case RuntimeComplexity:
                    return computeCostsForTimeAnalysis(e);
                case SpaceComplexity:
                    return computeCostsForSpaceAnalysis(e);
                case SizeComplexity:
                    return computeCostsForTermSizeAnalysis(e);
                case UserDefined:
                    return computeCostsForUsedDefinedAnalysis(e);
                default:
                    throw new RuntimeException();
                }
            }

            private Pair<SimplePolynomial, SimplePolynomial> computeCostsForUsedDefinedAnalysis(Edge e) {
                if (e.getLabel() instanceof PredefinedMethodEdge) {
                    PredefinedMethodEdge pme = (PredefinedMethodEdge) e.getLabel();
                    SimplePolynomial lowerBound = pme.getLowerTimeBound();
                    SimplePolynomial upperBound = pme.getUpperTimeBound();
                    return new Pair<>(lowerBound, upperBound);
                } else {
                    return new Pair<>(SimplePolynomial.ZERO, SimplePolynomial.ZERO);
                }
            }

            private Pair<SimplePolynomial, SimplePolynomial> computeCostsForTimeAnalysis(Edge e) {
                if (e.getLabel() instanceof PredefinedMethodEdge) {
                    PredefinedMethodEdge pme = (PredefinedMethodEdge) e.getLabel();
                    SimplePolynomial lowerBound = pme.getLowerTimeBound();
                    SimplePolynomial upperBound = pme.getUpperTimeBound();
                    return new Pair<>(lowerBound, upperBound);
                } else if (e.getLabel() instanceof EvaluationEdge) {
                    return new Pair<>(SimplePolynomial.ONE, SimplePolynomial.ONE);
                } else {
                    return new Pair<>(SimplePolynomial.ZERO, SimplePolynomial.ZERO);
                }
            }

            private Pair<SimplePolynomial, SimplePolynomial> computeCostsForSpaceAnalysis(Edge e) {
                if (e.getLabel() instanceof PredefinedMethodEdge) {
                    PredefinedMethodEdge pme = (PredefinedMethodEdge) e.getLabel();
                    SimplePolynomial lowerBound = pme.getLowerSpaceBound();
                    SimplePolynomial upperBound = pme.getUpperSpaceBound();
                    return new Pair<>(lowerBound, upperBound);
                } else  if (e.getLabel() instanceof EvaluationEdge) {
                    return computeSpaceCostsForEvaluationEdge(e);
                } else {
                    return new Pair<>(SimplePolynomial.ZERO, SimplePolynomial.ZERO);
                }
            }

            private Pair<SimplePolynomial, SimplePolynomial> computeSpaceCostsForEvaluationEdge(Edge e) {
                if (e.getStart().getState().getCurrentStackFrame().hasException()) {
                    return new Pair<>(SimplePolynomial.ZERO, SimplePolynomial.ZERO);
                }
                State s = e.getStart().getState();
                OpCode oc = s.getCurrentOpCode();
                if (e.getEnd().getState() != null) {
                    State end = e.getEnd().getState();
                    if (s.getCallStack().size() == end.getCallStack().size() - 1) {
                        if (end.getCallStack().get(1).hasException()) {
                            return new Pair<>(SimplePolynomial.ZERO, SimplePolynomial.ZERO);
                        }
                    }
                }
                SimplePolynomial cost;
                if (oc instanceof New) {
                    cost = SimplePolynomial.ONE;
                } else if (oc instanceof ArrayCreate) {
                    cost = computeSizeOfFreshArray(s, oc);
                } else {
                    cost = SimplePolynomial.ZERO;
                }
                return new Pair<>(cost, cost);
            }

            private Pair<SimplePolynomial, SimplePolynomial> computeCostsForTermSizeAnalysis(Edge e) {
                /* TODO
                 * This handling was originally created for non recursive cases, where the callStackEmpty singnalled the end of the analysis.
                 * Hence, the the cost of the edge were set the the size of the term we wanted to analyse.
                 *
                 * In Recursive functions, the callstackempty appears at the end of EVERY recursive call.
                 * Thus, the cost of the analysis are much larger.
                 * Creating a special rule for the outermost frame, or calling the recursive function from a non-recusive function could fix this.
                 *
                 * Until this is fixed the term size analysis for recursive programs will not yield accurate results!
                 */
                if (e.getEnd().getState().callStackEmpty()) {
                    State s = e.getStart().getState();
                    TRSTerm term;
                    ComplexityGoalTerm gt = goalTerm.orElse(ComplexityGoalTerm.RET);
                    if (gt != ComplexityGoalTerm.RET || e.getStart().getState().getCurrentOpCode() instanceof Return) {
                        Optional<AbstractVariableReference> ref = gt.getReferenceFromStackFrame(s.getCurrentStackFrame());
                        if (ref.isPresent()) {
                            if (ref.get().pointsToConstantInt()) {
                                SimplePolynomial cost = SimplePolynomial.create(ref.get().toLiteralInt().getLiteral());
                                return new Pair<>(cost, cost);
                            }
                            term = createVariable(ref.get());
                        } else {
                            term = gt.getTerm().get();
                        }
                        return new Pair<>(SimplePolynomial.create(term.getName()), SimplePolynomial.create(term.getName()));
                    }
                }
                return new Pair<>(SimplePolynomial.ZERO, SimplePolynomial.ZERO);
            }

            void addRhs(BasicNodeTransformation r) {
                right.add(r);
            }

            void applySubstitution(Map<TRSVariable, TRSVariable> sigma) {
                applySubstitutionToLeft(sigma);
                applySubstitutionToRight(sigma);
                applySubstitutionToCond(sigma);
                applySubstitutionToCosts(sigma);
            }

            void applySubstitutionToLeft(Map<TRSVariable, ? extends TRSTerm> sigma) {
                left.applySubstitution(sigma);
            }

            void applySubstitutionToCosts(Map<TRSVariable, TRSVariable> sigma) {
                Map<String, String> polySubst = new LinkedHashMap<>();
                for (Entry<TRSVariable, TRSVariable> e: sigma.entrySet()) {
                    polySubst.put(e.getKey().getName(), e.getValue().getName());
                }
                lowerBound = lowerBound.replace(polySubst);
                upperBound = upperBound.replace(polySubst);
            }

            void applySubstitutionToRight(Map<TRSVariable, ? extends TRSTerm> sigma) {
                right.forEach(r -> r.applySubstitution(sigma));
            }

            Rule asRule() {
                List<TRSFunctionApplication> rhs = right.stream().map(r -> r.t).collect(toList());
                ConjunctiveClause rightC = right.stream().map(r -> r.c).collect(
                        () -> new ConjunctiveClause(emptySet()),
                        (c1, c2) -> c1.and(c2),
                        (c1, c2) -> c1.and(c2));
                List<TRSTerm> lhsOutputVariables = new ArrayList<>(left.termOutputVariables);
                return new Rule(left.t, rhs, c.and(left.c.and(rightC)), lowerBound, upperBound, lhsOutputVariables);
            }

            void and(Literal l) {
                c = c.and(l);
            }

            void and(Condition cond) {
                c = c.and(cond);
            }

            public void applySubstitutionToCond(Map<TRSVariable, TRSVariable> sigma) {
                c = c.applySubstitution(sigma);
            }

        }

        private class BasicNodeTransformation {

            TRSFunctionApplication t;
            ConjunctiveClause c;
            Node node;
            Set<TRSTerm> termOutputVariables;

            BasicNodeTransformation(Node node, boolean withOutputVars) {
                this.node = node;
                Set<TRSTerm> args = buildArgs();
                Set<TRSTerm> allArgs = new LinkedHashSet<>(args);
                Set<TRSTerm> outputArgs = new LinkedHashSet<>();
                allArgs.add(ENV);
                allArgs.add(STATIC);
                if (withOutputVars && !node.getState().callStackEmpty()) {
                    StackFrame bottomFrame = node.getState().getCallStack().getFromBottom(1);
                    allArgs.addAll(sideEffectVars.getOrDefault(bottomFrame.getMethod(), emptyMap()).values());
                }
                for (TRSTerm arg: allArgs) {
                    if (!args.contains(arg)) {
                        outputArgs.add(arg);
                    }
                }
                TRSFunctionApplication t = buildTerm(allArgs);
                ConjunctiveClause c = buildCondition();
                this.t = t;
                this.c = c;
                this.termOutputVariables = outputArgs;
            }

            public BasicNodeTransformation(Node node) {
                this(node, args.targetSystem == TargetSystem.CES);
            }

            void applySubstitution(Map<TRSVariable, ? extends TRSTerm> sigma) {
                TRSSubstitution subst = TRSSubstitution.create(ImmutableCreator.create(sigma));
                t = t.applySubstitution(subst);
                c = c.applySubstitution(subst);
            }

            Set<TRSTerm> buildArgs() {
                Set<TRSTerm> args = new LinkedHashSet<>();
                getRefs().forEach(x -> args.add(createVariable(x)));
                return args;
            }

            Set<AbstractVariableReference> getRefs() {
                Set<AbstractVariableReference> refs = new LinkedHashSet<>(node.getState().getReferences().keySet());
                HeapPositions heapPos = new HeapPositions(node.getState(), true);
                Iterator<AbstractVariableReference> it = refs.iterator();
                REF: while (it.hasNext()) {
                    AbstractVariableReference x = it.next();
                    if (!isRelevant(x)) {
                        it.remove();
                        continue;
                    }
                    Collection<StatePosition> positions = heapPos.getPositionsForRef(x);
                    POS: for (StatePosition y: positions) {
                        Collection<HeapEdge> edges = y.getHeapEdges();
                        for (HeapEdge z: edges) {
                            if (z instanceof InstanceFieldEdge){
                                InstanceFieldEdge ife = (InstanceFieldEdge) z;
                                if (!isUsed(ife.getFieldIdentifier())){
                                    continue POS;
                                }
                            }
                        }
                        if (y.getRootPosition() instanceof StaticFieldRootPosition) {
                            StaticFieldRootPosition sfrp = (StaticFieldRootPosition) y.getRootPosition();
                            FieldIdentifier fid = new FieldIdentifier(sfrp.getClassName(), sfrp.getFieldName());
                            if (!isUsed(fid)) {
                                continue POS;
                            }
                        }
                        continue REF;
                    }
                    it.remove();
                }
                return refs;
            }

            boolean isRelevant(AbstractVariableReference ref) {
                return ref.pointsToConstant() || relevantRefs == null || relevantRefs.getNotNull(node).contains(ref);
            }

            TRSFunctionApplication buildTerm(Set<TRSTerm> args) {
                String name = buildName();
                int arity = args.size();
                FunctionSymbol f = FunctionSymbol.create(getValidName(name), arity);
                return TRSTerm.createFunctionApplication(f, new ArrayList<>(args));
            }

            String buildName() {
                State s = node.getState();
                String nodeNumber = Integer.toString(node.getNodeNumber());
                if (s.callStackEmpty()) {
                    return "END_" + nodeNumber;
                } else {
                    MethodIdentifier mid = s.getCurrentStackFrame().getMethod().getMethodIdentifier();
                    OpCode op = s.getCurrentOpCode();
                    return mid.getMethodName().replaceAll("<", "langle_").replaceAll(">", "_rangle") + "_" + op.getShortName() + "_" + nodeNumber;
                }
            }

            ConjunctiveClause buildCondition() {
                State s = node.getState();
                Set<AbstractVariableReference> refs = getRefs();
                ConjunctiveClause c = new ConjunctiveClause(emptySet());
                for (AbstractVariableReference r : refs) {
                    c = c.and(buildConstraints(s, r, createVariable(r)));
                }
                return c;
            }

            ConjunctiveClause buildConstraints(State s, AbstractVariableReference r, TRSTerm arg) {
                AbstractVariable val = s.getAbstractVariable(r);
                ConjunctiveClause res = new ConjunctiveClause(emptySet());
                if (val instanceof LiteralInt) {
                    LiteralInt lit = (LiteralInt) val;
                    if (lit.getLiteral().abs().compareTo(BigInteger.valueOf(Integer.MAX_VALUE)) < 0) {
                        res = res.and(Literal.eq(arg, buildInt(lit.getLiteral())));
                    }
                } else if (val instanceof IntervalInt) {
                    IntervalInt interval = (IntervalInt) val;
                    if (interval.getLower().isFinite()) {
                        res = res.and(Literal.le(buildInt(interval.getLower().getConstant()), arg));
                    }
                    if (interval.getUpper().isFinite()) {
                        res = res.and(Literal.le(arg, buildInt(interval.getUpper().getConstant())));
                    }
                } else if (!r.isNULLRef() && r.pointsToReferenceType()) {
                    if (s.getHeapAnnotations().isMaybeExisting(r)) {
                        res = res.and(Literal.nonNegative(createVariable(r)));
                    } else {
                        res = res.and(Literal.positive(createVariable(r)));
                    }
                }
                return res;
            }

            void removeLiteralsFor(TRSVariable var) {
                c = c.removeLiteralsFor(var);
            }
        }

        private class Predecessors {

            Set<AbstractVariableReference> abstractPreds;
            Set<AbstractVariableReference> concretePreds;
            Set<AbstractVariableReference> allPreds;

            Predecessors(State s, AbstractVariableReference r) {
                HeapPositions heapPos = new HeapPositions(s, true);
                HeapAnnotations annotations = s.getHeapAnnotations();
                concretePreds = new LinkedHashSet<>(heapPos.getAllPredecessors(r, true));
                abstractPreds = new LinkedHashSet<>();
                abstractPreds.addAll(annotations.getJoiningStructures().getReferencesWithPartner(r));
                abstractPreds.addAll(annotations.getEqualityGraph().getReferencesWithPartner(r));
                abstractPreds.removeAll(concretePreds);
                allPreds = union(abstractPreds, concretePreds);
            }

        }

        private class ReplacementMap {

            Map<AbstractVariableReference, TRSVariable> oldVars = new LinkedHashMap<>();
            Map<AbstractVariableReference, TRSVariable> newVars = new LinkedHashMap<>();
            Map<TRSVariable, TRSVariable> sigma;

            ReplacementMap(Predecessors preds) {
                Map<TRSVariable, TRSVariable> replacementMap = new LinkedHashMap<>();
                for (AbstractVariableReference r : preds.allPreds) {
                    TRSVariable x = createVariable(r);
                    TRSVariable y = createVariable(r, "'");
                    oldVars.put(r, x);
                    newVars.put(r, y);
                    replacementMap.put(x, y);
                }
                sigma = replacementMap;
            }

            ReplacementMap(Map<AbstractVariableReference, AbstractVariableReference> baseMap) {
                Map<TRSVariable, TRSVariable> replacementMap = new LinkedHashMap<>();
                for (Entry<AbstractVariableReference, AbstractVariableReference> entry : baseMap.entrySet()) {
                    TRSVariable x = createVariable(entry.getKey());
                    TRSVariable y = createVariable(entry.getValue());
                    oldVars.put(entry.getKey(), x);
                    newVars.put(entry.getKey(), y);
                    replacementMap.put(x, y);
                }
                sigma = replacementMap;
            }

            TRSVariable getOldVar(AbstractVariableReference r) {
                return oldVars.get(r);
            }

            TRSVariable getNewVar(AbstractVariableReference r) {
                return newVars.get(r);
            }

        }

        private JBCGraphEdgesComplexityProblem edges;
        private Map<IMethod, Map<StatePosition, TRSVariable>> sideEffectVars;
        private Optional<ComplexityGoalTerm> goalTerm;
        private UsedFieldsAnalysis ufa;
        private CollectionMap<Node, AbstractVariableReference> relevantRefs;
        private ClassPath cp;

        public RulesTransformer(JBCGraphEdgesComplexityProblem edges, UsedFieldsAnalysis ufa) {
            this.edges = edges;
            this.goalTerm = edges.getGoalTerm();
            this.ufa = ufa;
            this.relevantRefs = edges.getRelevantRefs();
            if (!edges.getEdgesToEncode().isEmpty()) {
                cp = edges.getEdgesToEncode().iterator().next().getStart().getState().getClassPath();
            }
            sideEffectVars = computeSideEffectVars();
        }

        private Map<IMethod, Map<StatePosition, TRSVariable>> computeSideEffectVars() {
            Map<IMethod, Map<StatePosition, TRSVariable>> res = new HashMap<>();
            Set<IMethod> calledMethods = getCalledMethods(edges);
            if (calledMethods.isEmpty()) {
                return res;
            }
            int counter = 0;

            for (Edge e : edges.getEdgesToEncode()) {
                if (e.getEnd().getState().callStackEmpty()) {
                    StackFrame sf = e.getStart().getState().getCurrentStackFrame();
                    IMethod currentMethod = sf.getMethod();
                    if (!calledMethods.contains(currentMethod)) {
                        continue;
                    }
                    Map<StatePosition, TRSVariable> currentMap = res.computeIfAbsent(currentMethod, k -> new LinkedHashMap<>());

                    if (sf.hasException()) {
                        currentMap.put(ExceptionRootPosition.create(-1), EXC);
                    } else if (!returnsVoidOrConstant(e.getStart().getState())) {
                        currentMap.put(OpStackRootPosition.create(0, 1), RET);
                    }

                    InputReferences inputReferences = sf.getInputReferences();
                    for (IRChangeInformations changes : inputReferences.getChangeInformations()) {
                        EnumMap<ChangeType, IrChangeInformation> summarisedChanges = changes.summariseAllChanges();
                        IrAddressChangeInformation addressChange = (IrAddressChangeInformation) summarisedChanges.get(ChangeType.ADDRESS);
                        StatePosition sPos = addressChange.getWritePosition();
                        if (addressChange.isChangeFromLowerFrame()) {
                            assert sPos == null;
                            sPos = addressChange.getChangeFromLowerFrame();
                        }
                        if (sPos != null) {
                            TRSVariable v = TRSVariable.createVariable("SEVar" + ++counter);
                            currentMap.put(sPos, v);
                        }
                    }
                }
            }
            return res;
        }

        private TRSVariable getSideEffectVariable(IMethod method, StatePosition sPos) {
            assert sPos != null;
            return sideEffectVars.getOrDefault(method, Collections.emptyMap()).get(sPos);
        }

        private boolean isUsed(FieldIdentifier fid) {
            // filtering fields is not sound for size complexity
            if (edges.getGoal() == HandlingMode.SizeComplexity) {
                return true;
            }
                if (args.filterFieldsOfTypeObject) {
                    for (Entry<String, Field> e: cp.getClass(fid.getClassName()).getInstanceFields().entrySet()) {
                        if (e.getKey().equals(fid.getFieldName())) {
                            FuzzyType type = FuzzyType.parseTypeDescriptor(e.getValue().getDescriptor());
                            if (type.equals(FuzzyClassType.FT_JAVA_LANG_OBJECT)) {
                                return false;
                            }
                        }
                    }
                }
            if (ufa == null) {
                return true;
            } else {
                return ufa.getUsedFieldNames(fid.getClassName()).contains(fid.getFieldName()) ||
                       ufa.getUsedStaticFieldNames(fid.getClassName()).contains(fid.getFieldName());
            }
        }

        public <R> Set<R> transformEdges(Function<Rule, Set<R>> converter) {
            Set<Rule> res = edgesToRules(edges);
            Set<R> rules = rulesToResRules(res, converter);
            return rules;
        }

        private Set<Rule> edgesToRules(JBCGraphEdgesComplexityProblem toTransform) {
            Set<Rule> res = new LinkedHashSet<>();
            getStartRule().ifPresent(res::add);
            for (Edge e : toTransform.getEdgesToEncode()) {
                transform(e).ifPresent(res::add);
            }
            return res;
        }

        private <R> Set<R> rulesToResRules(Set<Rule> rules, Function<Rule, Set<R>> converter) {
            Set<R> res = new LinkedHashSet<>();
            for (Rule r: rules) {
                res.addAll(converter.apply(r));
            }
            return res;
        }

        private Optional<Rule> transform(Edge e) {
            EdgeInformation info = e.getLabel();
            if (info instanceof EvaluationEdge) {
                return Optional.of(transformEvaluationEdge(e));
            } else if (info instanceof RefinementOrSplitEdge) {
                return Optional.of(transformRefinementOrSplitEdge(e));
            } else if (info instanceof InstanceEdge) {
                return Optional.of(transformInstanceEdge(e));
            } else if (info instanceof InitializationStateChange) {
                return Optional.of(transformInitializationStateChange(e));
            } else if (info instanceof MethodSkipEdge) {
                return transformMethodSkipEdge(e);
            } else if (info instanceof CallAbstractEdge) {
                return transformCallAbstractEdge(e);
            } else {
                throw new RuntimeException("unknown edge type");
            }
        }

        private Optional<Rule> transformCallAbstractEdge(Edge edge) {
            if (!args.alwaysGenerateCallEdges) {
                for (Edge out : edge.getStart().getOutEdges()) {
                    if (out.getLabel() instanceof MethodSkipEdge) {
                        return Optional.empty(); //call edge is encoded in method skip edge
                    }
                }
            }

            BasicEdgeTransformation bet = new BasicEdgeTransformation(edge);
            Map<TRSVariable, TRSVariable> sigma = buildEndToStartSubstitution(edge);
            bet.applySubstitutionToRight(sigma);
            return Optional.of(bet.asRule());
        }

        private Optional<Rule> transformMethodSkipEdge(Edge edge) {
            //check if there is a (chain of) outgoing instance edge with an incoming Methodskipedge, if so we can skip encoding this edge
            Node toCheck = edge.getEnd();
            while(true) {
                for (Edge out : toCheck.getOutEdges()) {
                    if (out.getLabel() instanceof InstanceEdge) {
                        toCheck = out.getEnd();
                        for (Edge in : toCheck.getInEdges()) {
                            if (in.getLabel() instanceof MethodSkipEdge) {
                                //there is a better edge to transform, we can skip this
                                return Optional.empty();
                            }
                        }
                        continue;//we might have more outgoing instances, keep looking
                    }
                }
                break; //no better edge found
            }

            //get the call Abstract edge
            Edge callAbstractEdge = null;
            for (Edge outEdge : edge.getStart().getOutEdges()) {
                if (outEdge.getLabel() instanceof CallAbstractEdge) {
                    callAbstractEdge = outEdge;
                    break;
                }
            }

            MethodSkipEdge methodSkipEdge = (MethodSkipEdge) edge.getLabel();

            State callingState = edge.getStart().getState();
            State methodSkipEndState = edge.getEnd().getState();
            State calledState = callAbstractEdge.getEnd().getState();
            State returnState = methodSkipEdge.getNode().getState();
            IMethod calledMethod = methodSkipEdge.getGraph().getParsedMethod();
            Map<AbstractVariableReference, AbstractVariableReference> callingToResultUnchanged = methodSkipEdge.getCallingToResultUnchangedMap();
            Map<AbstractVariableReference, Pair<AbstractVariableReference, AbstractVariableReference>> callToResultEndChanged = methodSkipEdge.getCallToResultEndChangedMap();

            //Rule
            BasicEdgeTransformation bet = new BasicEdgeTransformation(edge);
            BasicNodeTransformation afterCall = bet.right.iterator().next();
            //inner call
            BasicNodeTransformation called = new BasicNodeTransformation(callAbstractEdge.getEnd());

            TRSVariable innerRet = TRSTerm.createVariable("innerRet");
            called.applySubstitution(Collections.singletonMap(RET, innerRet));
            TRSVariable innerExc = TRSTerm.createVariable("innerExc");
            called.applySubstitution(Collections.singletonMap(EXC, innerExc));
            bet.addRhs(called);


            if (methodSkipEndState.getCurrentStackFrame().hasException()) {
                TRSVariable exception = createVariable(methodSkipEndState.getCurrentStackFrame().getException());
                bet.right.forEach(r -> r.removeLiteralsFor(exception));
                bet.and(Literal.eq(innerExc, exception));
            } else if (!returnsVoidOrConstant(methodSkipEndState)) {
                TRSVariable returnValue = createVariable(methodSkipEndState.getCurrentStackFrame().peekOperandStack(0));
                bet.right.forEach(r -> r.removeLiteralsFor(returnValue));
                bet.and(Literal.eq(innerRet, returnValue));
            }


            for (AbstractVariableReference ref : callingState.getReferences().keySet()) {
                if (callingToResultUnchanged.containsKey(ref)) { //no side effect, apply renaming
                    bet.applySubstitution(singletonMap(createVariable(ref), createVariable(callingToResultUnchanged.get(ref))));
                } else if (callToResultEndChanged.containsKey(ref)) { //side effect, find bounds
                    if (!ref.pointsToReferenceType()) {
                        continue; //primitve IRs are not intersting
                    }
                    Pair<AbstractVariableReference, AbstractVariableReference> resultEndRefPair = callToResultEndChanged.get(ref);
                    InputReference iR = findCorrespondingIr(returnState, resultEndRefPair.y);
                    assert iR != null;

                    List<TRSTerm> uBSummands = new ArrayList<>();
                    uBSummands.add(createVariable(ref));
                    boolean isSmaller = computeUpperBoundSummands(iR.getReference(), returnState, calledMethod, iR.getChanges(), uBSummands);

                    TRSVariable resultVar = createVariable(resultEndRefPair.x);
                    TRSTerm upperBound = buildSum(uBSummands);
                    if (isSmaller) {
                        bet.and(Literal.lt(resultVar, upperBound));
                    } else {
                        bet.and(Literal.le(resultVar, upperBound));
                    }

                } else {//there are references that have no IR in called state (i.e. primitives or predecessors)
                    if (!ref.pointsToReferenceType()) {//non references can't be modified
                        continue;
                    }

                    //these are references not visible in the called method, but they might be predecessors to changed IRs
                    Set<AbstractVariableReference> reachableRefs = reachableRefs(ref, callingState);

                    boolean foundChange = false;
                    IRChangeInformations changes = null;
                    for (AbstractVariableReference reachableRef : reachableRefs) {
                        Pair<AbstractVariableReference, AbstractVariableReference> resultEndRefPair = callToResultEndChanged.get(reachableRef);
                        if (resultEndRefPair == null) {
                            continue;
                        }
                        InputReference iR = findCorrespondingIr(returnState, resultEndRefPair.y);
                        assert iR != null;
                        if (foundChange) {
                            changes.merge(iR.getChanges());
                        } else {
                            changes = iR.getChanges().copy();
                            foundChange = true;
                        }
                    }

                    if (!foundChange) //no successor of the ref changed
                        continue; //var already has same name on RHS, so nothing more to do

                    //rename the variable on the rhs as it is no longer equal to the var on the lhs
                    TRSVariable originalVar = createVariable(ref);
                    TRSVariable resultVar = createVariable(ref, "'");
                    afterCall.applySubstitution(singletonMap(originalVar, resultVar));

                    //now computo an upper bound for the new variable
                    List<TRSTerm> uBSummands = new ArrayList<>();
                    uBSummands.add(originalVar);
                    boolean isSmaller = computeUpperBoundSummands(ref, callingState, calledMethod, changes, uBSummands); //if we would have not merged changes, we could hand in the ref of the changed IR and the returnState here for more precision

                    TRSTerm upperBound = buildSum(uBSummands);
                    if (isSmaller) {
                        bet.and(Literal.lt(resultVar, upperBound));
                    } else {
                        bet.and(Literal.le(resultVar, upperBound));
                    }
                }
            }

            //rename side effect vars on the rhs if we take them from the return state (this is not strictly necessary but should make the system easier to solve)
            for (IRChangeInformations changes : returnState.getInputReferences().getChangeInformations()) {
                EnumMap<ChangeType, IrChangeInformation> summarisedChanges = changes.summariseAllChanges();
                IrAddressChangeInformation addressChange = (IrAddressChangeInformation) summarisedChanges.get(ChangeType.ADDRESS);
                StatePosition sPos = addressChange.getWritePosition();
                if (addressChange.isChangeFromLowerFrame()) {
                    assert sPos == null;
                    sPos = addressChange.getChangeFromLowerFrame();
                }
                if (sPos != null) {
                    TRSVariable oldV = getSideEffectVariable(calledMethod, sPos);
                    TRSVariable newV = TRSTerm.createVariable(getValidName(oldV.getName() + "'"));
                    afterCall.applySubstitution(singletonMap(oldV, newV));
                }
            }

            //Handle changed static Fields TODO this code is similar to the one for reachableChanges, extract to common method
            boolean foundChangedSF = false;
            IRChangeInformations sFChanges = null;
            for (Entry<FieldIdentifier, IRChangeInformations> changedSF : returnState.getInputReferences().getChangedSF().entrySet()) {
                if (foundChangedSF) {
                    sFChanges.merge(changedSF.getValue());
                } else {
                    sFChanges = changedSF.getValue().copy();
                    foundChangedSF = true;
                }
            }
            if (foundChangedSF) {
                //rename the variable on the rhs as it is no longer equal to the var on the lhs
                TRSVariable originalVar = STATIC;
                TRSVariable resultVar = TRSVariable.createVariable("static'");
                afterCall.applySubstitution(singletonMap(originalVar, resultVar));

                //now compute an upper bound for the new variable
                List<TRSTerm> uBSummands = new ArrayList<>();
                uBSummands.add(originalVar);
                //TODO we could actually got through all static fields by there own, that would give us a ref
                boolean hasBound = computeUpperBoundSummands(null, callingState, calledMethod, sFChanges, uBSummands); //if we would have not merged changes, we could hand in the ref of the changed IR and the returnState here for more precision

                if (hasBound)
                    bet.and(Literal.le(resultVar, buildSum(uBSummands)));
            }

            /* TODO there are new references introduces that not correspond to changed IRs that we need an upper bound for
             * these usually come from refinements in the skipped method, so they should have some known parent we can use for UBs
             */
            //reverse to have the terms in "intuitive" order
            Collections.reverse(bet.right);
            return Optional.of(bet.asRule());
        }

        private InputReference findCorrespondingIr(State state, AbstractVariableReference ref) {
            for (InputReference candidate : state.getInputReferences()) {
                if (candidate.getReference().equals(ref)) {
                    return candidate;
                }
            }
            return null;
        }

        private boolean computeUpperBoundSummands(AbstractVariableReference ref, State state, IMethod method, IRChangeInformations changes, List<TRSTerm> res) {

            for (Entry<ChangeType, IrChangeInformation> change : changes.summariseAllChanges().entrySet()) {
                switch (change.getKey()) {
                case ADDRESS:
                    IrAddressChangeInformation addressChange = (IrAddressChangeInformation)change.getValue();
                    if (addressChange.isNullWrite()) {
                        //nothing to do, we are smaller and do not need to add summands
                    } else if (addressChange.isNewSuccOfOld()) {
                        //we are smaller, no summandsneeded
                    } else if (addressChange.isChangeFromLowerFrame()) {
                        TRSVariable var = getSideEffectVariable(method, addressChange.getChangeFromLowerFrame());
                        assert var != null;
                        res.add(var);
                    } else if (addressChange.getWrittenRef() != null) {
                        TRSVariable var = getSideEffectVariable(method, addressChange.getWritePosition());
                        assert var != null;
                        res.add(var);
                    } else {
                        return false; //unknown address actions
                    }
                    break;
                case FLOAT:
                    return false; //float action
                case INTEGER:
                    IrPrimitiveChangeInformation primitiveChange = (IrPrimitiveChangeInformation)change.getValue();

                    AbstractInt number = (AbstractInt) primitiveChange.getNewValue();
                    if (number.getUpper().isFinite() && number.getLower().isFinite()) {
                        BigInteger upper = number.getUpper().getConstant().abs();
                        BigInteger lower = number.getLower().getConstant().abs();
                        if (upper.compareTo(lower) >= 0)
                            res.add(buildInt(upper));
                        else
                            res.add(buildInt(lower));
                    } else {
                        return false;//infinite int action
                    }

                    break;
                } //end switch
            } //end for
            return true;
        }

        private Rule transformInitializationStateChange(Edge e) {
            BasicEdgeTransformation bet = new BasicEdgeTransformation(e);
            if (e.getLabel() instanceof InitializationStateChange) {
                InitializationStateChange isc = (InitializationStateChange) e.getLabel();
                for (Triple<ClassName, InitStatus, InitStatus> p: isc.getNewInitStates()) {
                    ClassName cname = p.x;
                    InitStatus initStatus = p.y;
                    if (initStatus != InitStatus.YES) {
                        continue;
                    }
                    State end = e.getEnd().getState();
                    State start = e.getStart().getState();
                    Set<AbstractVariableReference> startRefs = start.getReferences().keySet();
                    StaticFields sfs = end.getStaticFields();
                    if (sfs.getClasses().contains(cname)) {
                        for (String fname: sfs.getNames(cname)) {
                            AbstractVariableReference createdRef = sfs.get(cname, fname);
                            if (startRefs.contains(createdRef)) {
                                continue;
                            }
                            bet.and(Literal.le(buildInt(0), STATIC));
                            TRSVariable x = createVariable(createdRef);
                            bet.and(Literal.le(x, STATIC));
                            if (createdRef.pointsToAnyIntegerType()) {
                                bet.and(Literal.le(buildMinus(STATIC), x));
                            }
                            break;
                        }
                    }
                }
            }
            return bet.asRule();
        }

        private Rule transformRefinementOrSplitEdge(Edge e) {
            RefinementOrSplitEdge info = (RefinementOrSplitEdge) e.getLabel();
            Map<TRSVariable, TRSVariable> sigma = buildStartToEndSubstitution(info);
            BasicEdgeTransformation bet = new BasicEdgeTransformation(e);
            bet.applySubstitutionToLeft(sigma);
            if (info instanceof RealizationRefinementEdge) {
                bet.and(transformRealizationRefinementEdge((RealizationRefinementEdge) info, e.getEnd()));
            }
            bet.and(edgeInfoToCondition(e.getLabel(), e.getEnd().getState()).applySubstitution(sigma));
            return bet.asRule();
        }

        private Condition transformRealizationRefinementEdge(RealizationRefinementEdge info, Node end) {
            State s = end.getState();
            Map<AbstractVariableReference, AbstractVariableReference> map = info.getRefRenaming();
            Condition res = True;
            for (Entry<AbstractVariableReference, AbstractVariableReference> e: map.entrySet()) {
                AbstractVariableReference parent = e.getValue();
                AbstractVariable parentVar = s.getAbstractVariable(parent);
                if (parentVar instanceof ConcreteInstance) {
                    ConcreteInstance conc = (ConcreteInstance) parentVar;
                    Set<AbstractVariableReference> children = getAllChildren(conc);
                    boolean preciseEncoding = children.stream().allMatch(child -> child.pointsToReferenceType());
                    preciseEncoding &= isTree(parent, s) || (!mayBeOnCycle(parent, s) && children.size() <= 1);
                    preciseEncoding &= args.preciseTreeEncoding;
                    preciseEncoding &= relevantRefs == null || children.stream().allMatch(x -> relevantRefs.get(end).contains(x));
                    preciseEncoding &= s.isFullyRealized(parent);
                    if (preciseEncoding) {
                        Set<TRSTerm> childVars = new LinkedHashSet<>();
                        for (AbstractVariableReference child: children) {
                            childVars.add(createVariable(child));
                        }
                        TRSTerm sum = buildSum(ONE, buildSum(childVars));
                        TRSVariable pv = createVariable(parent);
                        res = res.and(Literal.eq(sum, pv));
                    } else {
                        for (AbstractVariableReference child: children) {
                            res = res.and(buildChildConstraints(parent, createVariable(parent), child,
                                    createVariable(child), s));
                        }
                    }
                } else if (parentVar instanceof Array) {
                    res = res.and(Literal.lt(createVariable(((Array) parentVar).getLength()), createVariable(parent)));
                }
            }
            return res;
        }

        private Set<AbstractVariableReference> getAllChildren(ConcreteInstance conc) {
            Set<AbstractVariableReference> children = new LinkedHashSet<>();
            for (Entry<FieldIdentifier, AbstractVariableReference> childEntry: conc.getAllFields().entrySet()) {
                FieldIdentifier field = childEntry.getKey();
                if (isUsed(field)) {
                    children.add(childEntry.getValue());
                }
            }
            return children;
        }

        private Map<TRSVariable, TRSVariable> buildStartToEndSubstitution(RefinementOrSplitEdge info) {
            Map<AbstractVariableReference, AbstractVariableReference> renaming;
            if (info instanceof RefinementEdge) {
                renaming = ((RefinementEdge) info).getRefRenaming();
            } else {
                renaming = Collections.emptyMap();
            }
            Map<TRSVariable, TRSVariable> replacementMap = new LinkedHashMap<>();
            for (Entry<AbstractVariableReference, AbstractVariableReference> entry : renaming.entrySet()) {
                replacementMap.put(createVariable(entry.getKey()), createVariable(entry.getValue()));
            }
            return replacementMap;
        }

        private Rule transformInstanceEdge(Edge e) {
            BasicEdgeTransformation bet = new BasicEdgeTransformation(e);
            Map<TRSVariable, TRSVariable> sigma = buildEndToStartSubstitution(e);
            bet.applySubstitutionToRight(sigma);
            return bet.asRule();
        }

        private Map<TRSVariable, TRSVariable> buildEndToStartSubstitution(Edge e) {
            CollectionMap<AbstractVariableReference, AbstractVariableReference> renaming = e.getRefRenamingEndToStart(null);
            Map<TRSVariable, TRSVariable> replacementMap = new LinkedHashMap<>();
            for (Entry<AbstractVariableReference, Collection<AbstractVariableReference>> entry : renaming.entrySet()) {
                AbstractVariableReference fromEnd = entry.getKey();
                Collection<AbstractVariableReference> s = entry.getValue();
                assert s.size() == 1;
                AbstractVariableReference fromStart = s.stream().findAny().get();
                replacementMap.put(createVariable(fromEnd), createVariable(fromStart));
            }
            return replacementMap;
        }

        private Rule transformEvaluationEdge(Edge e) {
            BasicEdgeTransformation bet = new BasicEdgeTransformation(e);
            State start = e.getStart().getState();
            State end = e.getEnd().getState();
            bet.and(edgeInfoToCondition(e.getLabel(), start));
            for (VariableInformation info : e.getLabel()) {
                if (info instanceof ReferenceAccessInformation) {
                    ReferenceAccessInformation access = (ReferenceAccessInformation) info;
                    if (access.isWrite()) {
                        Pair<Map<TRSVariable, TRSVariable>, Condition> p = processWrite(access, start, end);
                        bet.applySubstitutionToRight(p.x);
                        bet.and(p.y);
                    }
                } else if (info instanceof EnvrionmentChangeInformation) {
                    EnvrionmentChangeInformation envChange = (EnvrionmentChangeInformation) info;
                    TRSVariable newEnv = TRSTerm.createVariable("env'");
                    Map<TRSVariable, TRSVariable> sigma = singletonMap(ENV, newEnv);
                    bet.applySubstitutionToRight(sigma);
                    envChange.getLb().ifPresent(x -> bet.and(Literal.le(polyToTerm(x), newEnv)));
                    envChange.getUb().ifPresent(x -> bet.and(Literal.le(newEnv, polyToTerm(x))));
                } else if (info instanceof StaticFieldAccessInformation) {
                    StaticFieldAccessInformation access = (StaticFieldAccessInformation) info;
                    AbstractVariableReference readOrWrittenRef = access.getAccessedRef();
                    bet.and(Literal.le(buildInt(0), STATIC));
                    TRSVariable x = createVariable(readOrWrittenRef);
                    switch (access.getAccessType()) {
                    case WRITE:
                        TRSVariable newStatic = TRSTerm.createVariable("static'");
                        Map<TRSVariable, TRSVariable> sigma = singletonMap(STATIC, newStatic);
                        bet.applySubstitutionToRight(sigma);
                        if (readOrWrittenRef.pointsToAnyIntegerType()) {
                            Literal negative = Literal.le(newStatic, buildSum(STATIC, buildMinus(x)));
                            Literal nonNegative = Literal.le(newStatic, buildSum(STATIC, x));
                            switch (getSign(start, readOrWrittenRef)) {
                            case Negative: bet.and(negative);
                            break;
                            case NonNegative: bet.and(nonNegative);
                            break;
                            case Unknown:
                                Condition caseNegative = new Condition(negative).and(Literal.lt(x, buildInt(0)));
                                Condition caseNonNegative = new Condition(nonNegative).and(Literal.le(buildInt(0), x));
                                bet.and(caseNegative.or(caseNonNegative));
                                break;
                            default:
                                throw new RuntimeException();
                            }
                        } else {
                            bet.and(Literal.le(newStatic, buildSum(STATIC, x)));
                            bet.and(Literal.le(buildInt(0), x));
                        }
                        break;
                    case READ:
                        AbstractVariableReference res = end.getCurrentStackFrame().getOperandStack().peek(0);
                        TRSVariable resVar = createVariable(res);
                        bet.and(Literal.le(resVar, STATIC));
                        if (readOrWrittenRef.pointsToAnyIntegerType()) {
                            bet.and(Literal.le(buildMinus(STATIC), resVar));
                        } else {
                            bet.and(Literal.nonNegative(resVar));
                        }
                        break;
                    default:
                        throw new RuntimeException();
                    }
                }
            }
            if (e.getLabel() instanceof PredefinedMethodEdge) {
                PredefinedMethodEdge pfe = (PredefinedMethodEdge) e.getLabel();
                Map<TRSVariable, TRSVariable> sigma = new LinkedHashMap<>();
                for (Entry<AbstractVariableReference, AbstractVariableReference> entry: pfe.getRefRenaming().entrySet()) {
                    sigma.put(createVariable(entry.getKey()), createVariable(entry.getValue()));
                }
                bet.applySubstitutionToLeft(sigma);
                bet.applySubstitutionToCosts(sigma);
                bet.applySubstitutionToCond(sigma);
            }
            if (start.getCurrentOpCode() instanceof ArrayCreate) {
                OperandStack currentOperandStack = end.getCurrentStackFrame().getOperandStack();
                if (!currentOperandStack.getStack().isEmpty() && currentOperandStack.peek(0).pointsToArray()) {
                    SimplePolynomial bound = computeSizeOfFreshArray(start, start.getCurrentOpCode());
                    AbstractVariableReference newArrayRef = end.getCurrentStackFrame().getOperandStack().peek(0);
                    bet.and(Literal.eq(createVariable(newArrayRef), bound.toTerm()));
                }
            }
            //end of graph
            if (end.callStackEmpty()) {
                IMethod method = start.getCurrentStackFrame().getMethod();
                if (sideEffectVars.containsKey(method)) {
                    //handle exception/return value
                    if (start.getCurrentStackFrame().hasException()) {
                        assert sideEffectVars.get(method).containsValue(EXC);
                        TRSVariable exception = createVariable(start.getCurrentStackFrame().getException());
                        bet.and(Literal.eq(EXC, exception));
                    } else if (!returnsVoidOrConstant(start)) {
                        assert sideEffectVars.get(method).containsValue(RET);
                        AbstractVariableReference returnRef = start.getCurrentStackFrame().peekOperandStack(0);
                        TRSVariable returnValue = createVariable(returnRef);
                        bet.and(Literal.eq(RET, returnValue));
                    }

                    //handle side effects
                    for (IRChangeInformations changes : start.getInputReferences().getChangeInformations()) {
                        EnumMap<ChangeType, IrChangeInformation> summarisedChanges = changes.summariseAllChanges();
                        IrAddressChangeInformation addressChange = (IrAddressChangeInformation) summarisedChanges.get(ChangeType.ADDRESS);
                        AbstractVariableReference writtenRef = addressChange.getWrittenRef();
                        if (writtenRef != null) {
                            TRSVariable var = getSideEffectVariable(method, addressChange.getWritePosition());
                            assert getSideEffectVariable(method, addressChange.getWritePosition()) != null;
                            assert start.getReferences().keySet().contains(writtenRef);
                            bet.and(Literal.eq(var, createVariable(writtenRef)));
                        }
                    }
                }
            }
            return bet.asRule();
        }

        private boolean returnsVoidOrConstant(State s) {
            StackFrame sf = s.getCurrentStackFrame();
            if (sf.getMethod().getReturnType() == null) {
                return true;
            }
            return sf.peekOperandStack(0).pointsToConstant();
        }

        private Condition edgeInfoToCondition(EdgeInformation label, State s) {
            return label.stream().map(x -> transform(x, s)).reduce(True, (x, y) -> x.and(y));
        }

        private Pair<Map<TRSVariable, TRSVariable>, Condition> processWrite(ReferenceAccessInformation access,
                State start, State end) {
            if (access instanceof InstanceAccessInformation) {
                FieldIdentifier field = ((InstanceAccessInformation) access).getFieldIdentifier();
                if (!isUsed(field)) {
                    return new Pair<>(emptyMap(), True);
                }
            }
            AbstractVariableReference parent = access.getAccessedRef();
            AbstractVariableReference child = access.getReadOrWrittenRef();
            TRSVariable childVar = createVariable(child);
            Optional<TRSVariable> oldChildVar = Optional.empty();
            if (access instanceof InstanceAccessInformation && args.lowerBoundsForWriteAccesses ) {
                AbstractVariable instance = start.getAbstractVariable(parent);
                if (instance instanceof ConcreteInstance) {
                    ConcreteInstance concInstance = (ConcreteInstance) instance;
                    FieldIdentifier field = ((InstanceAccessInformation) access).getFieldIdentifier();
                    AbstractVariableReference oldChild = concInstance.getField(field.getClassName(), field.getFieldName());
                    if (oldChild != null && oldChild.pointsToReferenceType()) {
                        oldChildVar = Optional.of(createVariable(oldChild));
                    }
                }
            }
            Predecessors preds = new Predecessors(start, parent);
            ReplacementMap m = new ReplacementMap(preds);
            Sign sign = getSign(start, child);
            boolean hasStaticPred = !areDisjoint(start.getStaticFields().getValues(), preds.allPreds);
            Condition res = buildConditionForPreds(childVar, oldChildVar, preds.allPreds, m, sign, hasStaticPred);
            res = res.and(encodeTree(access, start, end, parent, child, m, preds));
            return new Pair<>(m.sigma, res);
        }

        // TODO use (some?) of the following optimizations for all predecessors
        private Condition encodeTree(ReferenceAccessInformation access, State start, State end,
                AbstractVariableReference parent, AbstractVariableReference child, ReplacementMap m,
                Predecessors preds) {
            Sign sign = getSign(start, child);
            TRSVariable childVar = createVariable(child);
            Condition res = True;
            if (access instanceof InstanceAccessInformation && end.getReferences().containsKey(parent)) {
                InstanceAccessInformation ia = (InstanceAccessInformation) access;
                AbstractVariable v = start.getAbstractVariable(parent);
                if (v instanceof ConcreteInstance) {
                    ConcreteInstance cv = (ConcreteInstance) v;
                    AbstractVariableReference oldChild = cv.getField(ia.getClassName(), ia.getFieldName());
                    TRSVariable oldChildVar = m.getOldVar(oldChild);
                    if (oldChildVar == null) {
                        oldChildVar = createVariable(oldChild);
                    }
                    TRSVariable parentVar = m.getOldVar(parent);
                    TRSVariable newParentVar = m.getNewVar(parent);
                    boolean treelike = isTree(parent, start) || (!mayBeOnCycle(parent, start) && start.isFullyRealized(parent) && getAllChildren(cv).size() <= 1);
                    if (child.pointsToReferenceType() && treelike && args.preciseTreeEncoding) {
                        Predecessors endPreds = new Predecessors(end, parent);
                        if (preds.concretePreds.contains(child)) {
                            if (oldChild.isNULLRef() || endPreds.concretePreds.contains(oldChild)) {
                                res = res.and(Literal.eq(newParentVar, parentVar));
                            } else if (!endPreds.abstractPreds.contains(oldChild)) {
                                res = res.and(Literal.eq(newParentVar, buildSum(parentVar, buildMinus(oldChildVar))));
                            }
                        } else if (!preds.abstractPreds.contains(child)) {
                            if (oldChild.isNULLRef() || endPreds.concretePreds.contains(oldChild)) {
                                res = res.and(Literal.eq(newParentVar, buildSum(parentVar, childVar)));
                            } else if (!endPreds.abstractPreds.contains(oldChild)) {
                                res = res.and(Literal.eq(newParentVar, buildSum(parentVar, childVar, buildMinus(oldChildVar))));
                            }
                        }
                    } else if (sign != Sign.Unknown && child.pointsToInteger()) {
                        if (start.checkIntegerRelation(oldChild, IntegerRelationType.EQ, child)) {
                            res = res.and(Literal.eq(newParentVar, parentVar));
                        }
                        if (sign == Sign.NonNegative) {
                            if (start.checkIntegerRelation(oldChild, IntegerRelationType.GT, child)) {
                                res = res.and(Literal.lt(newParentVar, parentVar));
                            } else if (start.checkIntegerRelation(oldChild, IntegerRelationType.GE, child)) {
                                res = res.and(Literal.le(newParentVar, parentVar));
                            } else if (start.checkIntegerRelation(oldChild, IntegerRelationType.LT, child)) {
                                res = res.and(Literal.lt(parentVar, newParentVar));
                            } else if (start.checkIntegerRelation(oldChild, IntegerRelationType.LE, child)) {
                                res = res.and(Literal.le(parentVar, newParentVar));
                            }
                        } else {
                            assert sign == Sign.Negative;
                            if (start.checkIntegerRelation(oldChild, IntegerRelationType.GT, child)) {
                                res = res.and(Literal.lt(parentVar, newParentVar));
                            } else if (start.checkIntegerRelation(oldChild, IntegerRelationType.GE, child)) {
                                res = res.and(Literal.le(parentVar, newParentVar));
                            } else if (start.checkIntegerRelation(oldChild, IntegerRelationType.LT, child)) {
                                res = res.and(Literal.lt(newParentVar, parentVar));
                            } else if (start.checkIntegerRelation(oldChild, IntegerRelationType.LE, child)) {
                                res = res.and(Literal.le(newParentVar, parentVar));
                            }
                        }
                    }
                }
            }
            return res;
        }

        private boolean isTree(AbstractVariableReference ref, State s) {
            if (s.getHeapAnnotations().isPossiblyNonTree(ref)) {
                return false;
            }
            Set<AbstractVariableReference> seen = new LinkedHashSet<>();
            Stack<AbstractVariableReference> todo = new Stack<>();
            todo.push(ref);
            do {
                AbstractVariableReference current = todo.pop();
                if (seen.add(current)) {
                    AbstractVariable var = s.getAbstractVariable(current);
                    if (var instanceof ConcreteInstance) {
                        ((ConcreteInstance) var).getAllFields()
                                                .values()
                                                .stream()
                                                .filter(x -> x.pointsToReferenceType() && !x.isNULLRef())
                                                .forEach(todo::push);
                    } else if (var instanceof ConcreteArray) {
                        ((ConcreteArray) var).getReferences()
                                             .keySet()
                                             .stream()
                                             .filter(x -> x.pointsToReferenceType() && !x.isNULLRef())
                                             .forEach(todo::push);
                    }
                } else {
                    return false;
                }
            } while (!todo.isEmpty());
            return true;
        }

        private Set<AbstractVariableReference> reachableRefs(AbstractVariableReference ref, State s) {
            Set<AbstractVariableReference> seen = new LinkedHashSet<>();
            Stack<AbstractVariableReference> todo = new Stack<>();
            todo.push(ref);
            do {
                AbstractVariableReference current = todo.pop();
                AbstractVariable var = s.getAbstractVariable(current);
                Collection<AbstractVariableReference> succs;
                if (var instanceof ConcreteInstance) {
                    succs = ((ConcreteInstance) var).getAllFields().values();
                } else if (var instanceof ConcreteArray) {
                    succs = ((ConcreteArray) var).getReferences().keySet();
                } else {
                    succs = emptySet();
                }
                succs
                .stream()
                .filter(x -> x.pointsToReferenceType() && !x.isNULLRef())
                .forEach(x -> {
                    if (seen.add(x)) todo.push(x);
                 });
            } while (!todo.isEmpty());
            return seen;
        }

        private boolean mayBeOnCycle(AbstractVariableReference ref, State s) {
            OUTER: if (s.getHeapAnnotations().getCyclicStructures().isCyclic(ref)) {
                for (HeapEdge e: s.getHeapAnnotations().getCyclicStructures().getNeededEdgesOf(ref)) {
                    assert e instanceof InstanceFieldEdge;
                    InstanceFieldEdge ifa = (InstanceFieldEdge) e;
                    if (!isUsed(ifa.getFieldIdentifier())) {
                        break OUTER;
                    }
                }
                return true;
            }
            return reachableRefs(ref, s).contains(ref);
        }

        private Condition buildConditionForPreds(TRSVariable var,
                Optional<TRSVariable> oldChildVar,
                Set<AbstractVariableReference> preds,
                ReplacementMap m,
                Sign sign,
                boolean staticPreds) {
            Condition res = True;
            Condition lowerBounds = True;
            ConjunctiveClause casePositive = new ConjunctiveClause(Literal.positive(var));
            ConjunctiveClause caseNonPositive = new ConjunctiveClause(Literal.nonPositive(var));
            for (AbstractVariableReference r : preds) {
                switch (sign) {
                case NonNegative:
                    res = res.and(Literal.le(m.getNewVar(r), buildSum(m.getOldVar(r), var)));
                    break;
                case Negative:
                    res = res.and(Literal.le(m.getNewVar(r), buildSum(m.getOldVar(r), buildMinus(var))));
                    break;
                case Unknown:
                    casePositive = casePositive.and(Literal.le(m.getNewVar(r), buildSum(m.getOldVar(r), var)));
                    caseNonPositive = caseNonPositive.and(Literal.le(m.getNewVar(r), buildSum(m.getOldVar(r), buildMinus(var))));
                    break;
                default:
                    throw new RuntimeException("unknown sign");
                }
                if (oldChildVar.isPresent()) {
                    lowerBounds = lowerBounds.and(Literal.le(buildSum(m.getOldVar(r), buildMinus(oldChildVar.get())), m.getNewVar(r)));
                }
            }
            if (staticPreds) {
                TRSVariable newStatic = TRSTerm.createVariable("static'");
                switch (sign) {
                case NonNegative:
                    res = res.and(Literal.le(newStatic, buildSum(STATIC, var)));
                    break;
                case Negative:
                    res = res.and(Literal.le(newStatic, buildSum(STATIC, buildMinus(var))));
                    break;
                case Unknown:
                    casePositive = casePositive.and(Literal.le(newStatic, buildSum(STATIC, var)));
                    caseNonPositive = caseNonPositive.and(Literal.le(newStatic, buildSum(STATIC, buildMinus(var))));
                    break;
                default:
                    throw new RuntimeException("unknown sign");
                }
                if (oldChildVar.isPresent()) {
                    lowerBounds = lowerBounds.and(Literal.le(buildSum(STATIC, buildMinus(oldChildVar.get())), newStatic));
                }
            }
            if (sign == Sign.Unknown) {
                res = casePositive.or(caseNonPositive);
            }
            return res.and(lowerBounds);
        }

        private Sign getSign(State s, AbstractVariableReference child) {
            if (child.pointsToAnyIntegerType()) {
                boolean nonNegative = s.checkIntegerRelation(new JBCIntegerRelation(child, IntegerRelationType.GE, AbstractInt.getZero()));
                if (nonNegative) {
                    return Sign.NonNegative;
                }
                boolean negative = s.checkIntegerRelation(new JBCIntegerRelation(child, IntegerRelationType.LE, AbstractInt.getZero()));
                if (negative) {
                    return Sign.Negative;
                }
                return Sign.Unknown;
            } else {
                return Sign.NonNegative;
            }
        }

        private Condition transform(VariableInformation info, State s) {
            if (info instanceof AbstractArrayAccessInformation || info instanceof AbstractInstanceAccessInformation) {
                return transform((ReferenceAccessInformation) info, s);
            } else if (info instanceof JBCIntegerRelation) {
                return transform((JBCIntegerRelation) info);
            } else if (info instanceof IntegerResultInformation) {
                return transform((IntegerResultInformation) info, s);
            } else if (info instanceof ObjectCreationInformation) {
                return transform((ObjectCreationInformation) info);
            } else if (info instanceof SizeRelationInformation) {
                return transform((SizeRelationInformation) info);
            } else {
                return True;
            }
        }

        private Condition transform(SizeRelationInformation info) {
            TRSVariable lhs = createVariable(info.getLhs());
            TRSTerm rhs = polyToTerm(info.getRhs());
            switch (info.getRel()) {
            case EQ: return new Condition(Literal.eq(lhs, rhs));
            case GE: return new Condition(Literal.le(rhs, lhs));
            case GT: return new Condition(Literal.lt(rhs, lhs));
            case LE: return new Condition(Literal.le(lhs, rhs));
            case LT: return new Condition(Literal.lt(lhs, rhs));
            case NE: return new Condition(Literal.neq(lhs, rhs));
            default: throw new RuntimeException();
            }
        }

        private Condition transform(ReferenceAccessInformation info, State s) {
            if (info.isRead()) {
                if (info instanceof InstanceAccessInformation) {
                    FieldIdentifier field = ((InstanceAccessInformation) info).getFieldIdentifier();
                    if (!isUsed(field)) {
                        return True;
                    }
                }
                AbstractVariableReference parent = info.getAccessedRef();
                AbstractVariableReference child = info.getReadOrWrittenRef();
                return buildChildConstraints(parent, createVariable(parent), child, createVariable(child), s);
            } else {
                return True;
            }
        }

        // TODO rename
        private Condition buildChildConstraints(AbstractVariableReference parent, TRSVariable parentVar,
                AbstractVariableReference child, TRSVariable childVar, State s) {
            BiFunction<TRSTerm, TRSTerm, Literal> rel;
            boolean cyclic = s.getHeapAnnotations().getCyclicStructures().isCyclic(parent);
            if (cyclic) {
                Set<HeapEdge> edges = s.getHeapAnnotations().getCyclicStructures().getNeededEdgesOf(parent);
                for (HeapEdge e: edges) {
                    if (e instanceof InstanceFieldEdge) {
                        InstanceFieldEdge ife = (InstanceFieldEdge) e;
                        if (!isUsed(ife.getFieldIdentifier())) {
                            cyclic = false;
                            break;
                        }
                    }
                }
            }
            if (cyclic) {
                rel = Literal::le;
            } else {
                rel = Literal::lt;
            }
            Condition res = new Condition(rel.apply(childVar, parentVar));
            if (child.pointsToAnyIntegerType()) {
                res = res.and(rel.apply(buildMinus(parentVar), childVar));
            }
            return res;
        }

        private Condition transform(ObjectCreationInformation info) {
            TRSVariable var = createVariable(info.getRef());
            return new Condition(Literal.eq(var, ONE));
        }

        private Condition transform(IntegerResultInformation info, State s) {
            Condition cond = True;
            Optional<TRSTerm> secondArg = transformSecondArg(info);
            if (secondArg.isPresent()) {
                AbstractVariableReference resRef = info.getResult();
                TRSVariable resVar = createVariable(resRef);
                switch (info.getArithmeticOperationType()) {
                case TIDIV: {
                    AbstractVariableReference first = info.getFirstNumber();
                    TRSTerm firstTerm = createVariable(first);
                    boolean dividentPositive = s.checkIntegerRelation(new JBCIntegerRelation(first, IntegerRelationType.GT, AbstractInt.getZero()));
                    boolean dividentNegative = s.checkIntegerRelation(new JBCIntegerRelation(first, IntegerRelationType.LT, AbstractInt.getZero()));
                    boolean dividentNonNegative = s.checkIntegerRelation(new JBCIntegerRelation(first, IntegerRelationType.GE, AbstractInt.getZero()));
                    boolean dividentNonPositive = s.checkIntegerRelation(new JBCIntegerRelation(first, IntegerRelationType.LE, AbstractInt.getZero()));
                    boolean dividentZero = s.checkIntegerRelation(new JBCIntegerRelation(first, IntegerRelationType.EQ, AbstractInt.getZero()));
                    boolean divisorPositive;
                    boolean divisorNegative;
                    boolean divisorGtOne;
                    boolean divisorLtMinusOne;
                    if (info.secondIsConstant()) {
                        AbstractInt divisor = info.getSecondConstant();
                        assert divisor.isLiteral();
                        divisorPositive = divisor.getLiteral().compareTo(BigInteger.ZERO) > 0;
                        divisorNegative = divisor.getLiteral().compareTo(BigInteger.ZERO) < 0;
                        divisorGtOne = divisor.getLiteral().compareTo(BigInteger.ONE) > 0;
                        divisorLtMinusOne = divisor.getLiteral().compareTo(BigInteger.ONE.negate()) < 0;
                    } else {
                        AbstractVariableReference divisor = info.getSecondNumber();
                        divisorPositive = s.checkIntegerRelation(new JBCIntegerRelation(divisor, IntegerRelationType.GT, AbstractInt.getZero()));
                        divisorNegative = s.checkIntegerRelation(new JBCIntegerRelation(divisor, IntegerRelationType.LT, AbstractInt.getZero()));
                        divisorGtOne = s.checkIntegerRelation(new JBCIntegerRelation(divisor, IntegerRelationType.GT, AbstractInt.getOne()));
                        divisorLtMinusOne = s.checkIntegerRelation(new JBCIntegerRelation(divisor, IntegerRelationType.LT, AbstractInt.getMOne()));
                    }
                    if (dividentZero) {
                        cond = cond.and(Literal.eq(resVar, firstTerm));
                    } else if (divisorGtOne) {
                        if (dividentPositive) {
                            cond = cond.and(Literal.lt(resVar, firstTerm));
                        } else if (dividentNegative) {
                            cond = cond.and(Literal.lt(firstTerm, resVar));
                        } else if (dividentNonNegative) {
                            cond = cond.and(Literal.le(resVar, firstTerm));
                        } else if (dividentNonPositive) {
                            cond = cond.and(Literal.le(firstTerm, resVar));
                        }
                    } else if (divisorPositive) {
                        if (dividentNonNegative) {
                            cond = cond.and(Literal.le(firstTerm, resVar));
                        } else if (dividentNonPositive) {
                            cond = cond.and(Literal.le(resVar, firstTerm));
                        }
                    } else if (divisorLtMinusOne) {
                        TRSTerm minusResVar = buildMinus(resVar);
                        if (dividentPositive) {
                            cond = cond.and(Literal.lt(minusResVar, firstTerm));
                        } else if (dividentNegative) {
                            cond = cond.and(Literal.lt(firstTerm, minusResVar));
                        } else if (dividentNonNegative) {
                            cond = cond.and(Literal.le(minusResVar, firstTerm));
                        } else if (dividentNonPositive) {
                            cond = cond.and(Literal.le(firstTerm, minusResVar));
                        }
                    } else if (divisorNegative) {
                        TRSTerm minusResVar = buildMinus(resVar);
                        if (dividentNonNegative) {
                            cond = cond.and(Literal.le(minusResVar, firstTerm));
                        } else if (dividentNonPositive) {
                            cond = cond.and(Literal.le(firstTerm, minusResVar));
                        }
                    }
                    if (args.simpleDivModEncoding) {
                        return cond;
                    }
                    break;
                }
                case TMOD: {
                    AbstractVariableReference first = info.getFirstNumber();
                    boolean dividentNonNegative = s.checkIntegerRelation(new JBCIntegerRelation(first, IntegerRelationType.GE, AbstractInt.getZero()));
                    boolean dividentNonPositive = s.checkIntegerRelation(new JBCIntegerRelation(first, IntegerRelationType.LE, AbstractInt.getZero()));
                    boolean dividentZero = s.checkIntegerRelation(new JBCIntegerRelation(first, IntegerRelationType.EQ, AbstractInt.getZero()));
                    if (dividentZero) {
                        cond = cond.and(Literal.eq(resVar, ZERO));
                    } else if (dividentNonNegative) {
                        cond = cond.and(Literal.lt(resVar, secondArg.get()));
                        cond = cond.and(Literal.le(ZERO, resVar));
                    } else if (dividentNonPositive) {
                        cond = cond.and(Literal.lt(secondArg.get(), resVar));
                        cond = cond.and(Literal.le(resVar, ZERO));
                    }
                    if (args.simpleDivModEncoding ) {
                        return cond;
                    }
                    break;
                }
                default: // do nothing
                }
                Optional<TRSFunctionApplication> op = buildOp(info, secondArg.get());
                if (op.isPresent()) {
                    return new Condition(Literal.eq(op.get(), resVar));
                }
            }
            return cond;
        }

        private Optional<TRSTerm> transformSecondArg(IntegerResultInformation info) {
            TRSTerm secondTerm;
            if (info.secondIsConstant()) {
                AbstractInt secondInt = info.getSecondConstant();
                if (secondInt.isLiteral()) {
                    secondTerm = buildInt(secondInt.getLiteral());
                } else {
                    return Optional.empty();
                }
            } else {
                AbstractVariableReference second = info.getSecondNumber();
                secondTerm = createVariable(second);
            }
            return Optional.of(secondTerm);
        }

        private Optional<TRSFunctionApplication> buildOp(IntegerResultInformation info, TRSTerm secondTerm) {
            TRSFunctionApplication op;
            if (info.getArithmeticOperationType() == ArithmeticOperationType.NEG) {
                op = TRSTerm.createFunctionApplication(Func.UnaryMinus.asFunctionSymbol(), secondTerm);
            } else {
                AbstractVariableReference first = info.getFirstNumber();
                TRSTerm firstTerm = createVariable(first);
                FunctionSymbol operand;
                switch (info.getArithmeticOperationType()) {
                case SUB:
                    operand = Func.Sub.asFunctionSymbol();
                    break;
                case MUL:
                    operand = Func.Mul.asFunctionSymbol();
                    break;
                case TIDIV:
                    operand = Func.Div.asFunctionSymbol();
                    break;
                case TMOD:
                    operand = Func.Mod.asFunctionSymbol();
                    break;
                case ADD:
                    operand = Func.Add.asFunctionSymbol();
                    break;
                default:
                    return Optional.empty();
                }
                op = TRSTerm.createFunctionApplication(operand, firstTerm, secondTerm);
            }
            return Optional.of(op);
        }

        private Condition transform(JBCIntegerRelation info) {
            Optional<TRSTerm> left = transformLeft(info);
            Optional<TRSTerm> right = transformRight(info);
            if (left.isPresent() && right.isPresent()) {
                return transformRel(left.get(), info.getRelationType(), right.get());
            } else {
                return True;
            }
        }

        private Optional<TRSTerm> transformLeft(JBCIntegerRelation info) {
            TRSTerm left;
            if (info.leftIntegerIsNoRef()) {
                AbstractInt leftInt = info.getLeftInt();
                if (leftInt.isLiteral()) {
                    left = buildInt(leftInt.getLiteral());
                } else {
                    return Optional.empty();
                }
            } else {
                AbstractVariableReference leftRef = info.getLeftIntRef();
                left = createVariable(leftRef);
            }
            return Optional.of(left);
        }

        Optional<TRSTerm> transformRight(JBCIntegerRelation info) {
            TRSTerm right;
            if (info.rightIntegerIsNoRef()) {
                AbstractInt rightInt = info.getRightInt();
                if (rightInt.isLiteral()) {
                    right = buildInt(rightInt.getLiteral());
                } else {
                    return Optional.empty();
                }
            } else {
                AbstractVariableReference rightRef = info.getRightIntRef();
                right = createVariable(rightRef);
            }
            return Optional.of(right);
        }

        private Condition transformRel(TRSTerm lhs, IntegerRelationType rel, TRSTerm rhs) {
            TRSFunctionApplication res;
            switch (rel) {
            case NE:
                res = buildNot(buildEq(lhs, rhs));
                break;
            case LT:
                res = buildLt(lhs, rhs);
                break;
            case LE:
                res = buildLe(lhs, rhs);
                break;
            case GT:
                res = buildLt(rhs, lhs);
                break;
            case GE:
                res = buildLe(rhs, lhs);
                break;
            case EQ:
                res = buildEq(lhs, rhs);
                break;
            default:
                throw new RuntimeException("unknown integer relation type");
            }
            return new Condition(new Literal(res));
        }

        public TRSFunctionApplication getStart(boolean useVariableNames, boolean withOutputVars) {
            State startState = edges.getStartNode().getState();
            OpCode oc = startState.getCurrentOpCode();
            IMethod method = oc.getMethod();
            StackFrame sf = startState.getCurrentStackFrame();
            Map<TRSVariable, TRSTerm> subst = new LinkedHashMap<>();
            for (int i: method.getActiveVariables(oc.getPos())) {
                String varName = null;
                if (useVariableNames) {
                    varName = method.getLocalVariableName(i, oc.getPos());
                }
                if (varName == null) {
                    if (!method.isStatic()) {
                        if (i==0)
                            varName = "this";
                        else
                            varName = "arg" + (i-1);
                    } else {
                        varName = "arg" + i;
                    }
                }
                subst.put(TRSTerm.createVariable(sf.getLocalVariable(i).toString()), TRSTerm.createVariable(varName));
            }
            TRSSubstitution sigma = TRSSubstitution.create(ImmutableCreator.create(subst));
            return new BasicNodeTransformation(edges.getStartNode(), withOutputVars).t.applySubstitution(sigma);
        }

        private Optional<Rule> getStartRule() {
            if (args.targetSystem != TargetSystem.CES)
                return Optional.empty();
            TRSFunctionApplication lhs = getStart(true, false);
            TRSFunctionApplication rhs = getStart(true, true);
            BasicNodeTransformation lBasicNodeTransformation = new BasicNodeTransformation(edges.getStartNode(), false);
            List<TRSTerm> lhsOutputVariables = new ArrayList<>(lBasicNodeTransformation.termOutputVariables); //getOutputVariables(edges.getStartNode().getState(), lhs);
            return Optional.of(new Rule(lhs, Collections.singletonList(rhs), True, SimplePolynomial.ZERO, SimplePolynomial.ZERO, lhsOutputVariables));
        }
    }

    private static TRSTerm polyToTerm(SimplePolynomial poly) {
        Set<String> vars = poly.getVariables();
        Map<String, String> replacementMap = new LinkedHashMap<>();
        vars.stream().forEach(x -> replacementMap.put(x, getValidName(x)));
        return poly.replace(replacementMap).toTerm();
    }

    private static String getValidName(String s) {
        String res = s;
        for (Entry<String, String> e: forbiddenSubStrings.entrySet()) {
            res = res.replace(e.getKey(), e.getValue());
        }
        return res;
    }

    protected static TRSVariable createVariable(AbstractVariableReference ref) {
        return createVariable(ref, "");
    }

    protected static TRSVariable createVariable(AbstractVariableReference ref, String postfix) {
        return TRSTerm.createVariable(getValidName(ref.toString() + postfix));
    }

    private static SimplePolynomial computeSizeOfFreshArray(State s, OpCode oc) {
        SimplePolynomial costs;
        ArrayCreate ac = (ArrayCreate) oc;
        int dimension = ac.getNumberOfArguments();
        costs = SimplePolynomial.ONE;
        OperandStack os = s.getCurrentStackFrame().getOperandStack();
        for (int i = 0; i < dimension; i++) {
            AbstractVariableReference r = os.peek(i);
            if (r.pointsToConstantInt()) {
                LiteralInt lit = (LiteralInt) s.getAbstractVariable(r);
                BigInteger val = BigInteger.valueOf(lit.getLongValue());
                costs = costs.times(SimplePolynomial.create(val).plus(SimplePolynomial.ONE));
            } else {
                costs = costs.times(SimplePolynomial.create(r.toString()).plus(SimplePolynomial.ONE));
            }
        }
        return costs.plus(SimplePolynomial.ONE);
    }

    protected static UsedFieldsAnalysis getUfa(SCCAnnotations annotations) {
        for (SCCAnalysis analysis: annotations.getAnalyses()) {
            if (analysis instanceof UsedFieldsAnalysis) {
                return (UsedFieldsAnalysis) analysis;
            }
        }
        return null;
    }

    @ParamsViaArgumentObject
    public JBCGraphEdgesToIntTrsProcessor(Arguments args) {
        this.args = args;
    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) {
        JBCGraphEdgesComplexityProblem edges = (JBCGraphEdgesComplexityProblem) obl;
        UsedFieldsAnalysis ufa = getUfa(edges.getSCCAnnotations());

        RulesTransformer rulesTransformer = new RulesTransformer(edges, ufa);
        TRSFunctionApplication start = rulesTransformer.getStart(true, false);

        BasicObligation newObl;
        Implication imp;
        int size;
        switch(args.targetSystem) {
        case IntTrs: {
            Set<WeightedRule> rules = rulesTransformer.transformEdges(x -> x.filterUnneededConditions().toWeightedRules());
            size = rules.size();
            String mName = edges.getStartNode().getState().getTerminationGraph().getStartGraph().getStartNode().getState().getCurrentStackFrame().getMethod().getName();
            newObl = new WeightedIntTrs(rules, start, mName, edges.consideredPaths());
            if (args.propagateLowerBounds()) {
                imp = SoundUpperUnsoundLowerBound.forConcreteBounds();
            } else {
                imp = UpperBound.forConcreteBounds();
            }
            break;
        }
        case IRS: {
            Set<IGeneralizedRule> rules = rulesTransformer.transformEdges(x -> x.toIRSRules());
            size = rules.size();
            newObl = new IRSProblem(ImmutableCreator.create(rules), start);
            imp = YNMImplication.SOUND;
            break;
        }
        case CES: {
            Set<CostEquation> equations = rulesTransformer.transformEdges(x -> x.filterUnneededConditions().toCostEquation());
            size = equations.size();
            String mName = edges.getStartNode().getState().getTerminationGraph().getStartGraph().getStartNode().getState().getCurrentStackFrame().getMethod().getName();
            newObl = new CostEquationSystem(mName, start, equations);
            imp = SoundUpperUnsoundLowerBound.forConcreteBounds();
            break;
        }
        default:
            assert false;
            return null;
        }
        return ResultFactory.proved(newObl, imp, new JBCGraphEdgesToCpxIntTrsProof(size, edges.getEdgesToEncode().size()));
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        if (!(obl instanceof JBCGraphEdgesComplexityProblem))
            return false;
        JBCGraphEdgesComplexityProblem edges = (JBCGraphEdgesComplexityProblem)obl;
        if (args.targetSystem == TargetSystem.CES) {
            return edges.consideredPaths() == ConsideredPaths.NONTERM_PATHS_AND_PATHS_FROM_START_TO_SINKS;
        } else {
            return getCalledMethods(edges).isEmpty();
        }
    }

    private static Set<IMethod> getCalledMethods(JBCGraphEdgesComplexityProblem obl) {
        Set<IMethod> calledMethods = new HashSet<>();
        for (Edge e : obl.getEdgesToEncode()) {
            if (e.getLabel() instanceof CallAbstractEdge) {
                calledMethods.add(e.getEnd().getState().getCurrentStackFrame().getMethod());
            }
        }
        return calledMethods;
    }

    private static boolean containsCallsWithSideEffects(JBCGraphEdgesComplexityProblem obl) {
        Set<IMethod> calledMethods = getCalledMethods(obl);
        if (calledMethods.isEmpty()) {
            return false; //there are no method calls
        }
        //now check for each end state in the called methods if they had side effects
        for (Edge e : obl.getEdgesToEncode()) {
            if (e.getEnd().getState().callStackEmpty()) {
                StackFrame sf = e.getStart().getState().getCurrentStackFrame();
                if (!calledMethods.contains(sf.getMethod())) {
                    continue; //this method is never called
                }
                InputReferences inputReferences = sf.getInputReferences();
                if (!inputReferences.getChangedSF().isEmpty()) {
                    return true; //side effect detected
                }
                for (InputReference iR : inputReferences) {
                    if (iR.getChanged()) {
                        return true; //side effect detected
                    }
                }
            }
        }
        return false;
    }

    public class JBCGraphEdgesToCpxIntTrsProof extends DefaultProof {

        private int itsSize;
        private int numEdges;

        public JBCGraphEdgesToCpxIntTrsProof(int itsSize, int numEdges) {
            this.itsSize = itsSize;
            this.numEdges = numEdges;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder res = new StringBuilder();
            res.append(o.escape("Transformed " + numEdges
                                + " jbc graph edges to "
                                + args.targetSystem.text
                                + " with "
                                + itsSize
                                + " rules."));
            if (args.simpleDivModEncoding) {
                res.append(o.newline());
                res.append(o.escape("Used simplified encoding of division and modulo."));
            }
            if (args.filterUnneededConditions) {
                res.append(o.newline());
                res.append(o.escape("Filtered conditions with variables that do not depend on the variables on the lhs or rhs"));
                if (!args.computeTransitiveClosureOfRelevantConditions) {
                    res.append(o.escape(" without taking transitive dependencies into account"));
                }
                res.append(".");
            }
            if (args.filterFieldsOfTypeObject) {
                res.append(o.newline());
                res.append(o.escape("Filtered fields of type java.lang.Object."));
            }
            if (!args.lowerBoundsForWriteAccesses) {
                res.append(o.newline());
                res.append(o.escape("Did no encode lower bounds for putfield and astore."));
            }
            return res.toString();
        }

    }

}
