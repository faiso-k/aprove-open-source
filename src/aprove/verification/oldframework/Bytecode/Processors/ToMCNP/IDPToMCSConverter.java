package aprove.verification.oldframework.Bytecode.Processors.ToMCNP;


import java.math.*;
import java.util.*;

import aprove.*;
import aprove.solver.Engines.*;
import aprove.solver.Engines.SMTEngine.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.idpGraph.*;
import aprove.verification.dpframework.IDPProblem.itpf.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.dpframework.MCSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntComparison.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;


/**
 *
 * @author Matthias Hoelzel
 *
 */
public class IDPToMCSConverter {
    /**
     * The given IDP
     */
    private IDPProblem idp;

    /**
     * IDP's P
     */
    private Set<GeneralizedRule> idpP;

    /**
     * IDP's R
     */
    private Set<GeneralizedRule> idpR;

    /**
     * The dependency graph
     */
    private IIDependencyGraph graph;

    /**
     * Set of IDP-Edges
     */
    private Set<IdpEdge> idpEdges;

    /**
     * The holy predefined map
     */
    private IDPPredefinedMap predefinedMap;

    /**
     * ITerm rewriter
     */
    private ITermRewriter iTermRewriter;

    /**
     * BTerm rewriter
     */
    private BTermRewriter bTermRewriter;

    /**
     * Stores the result.
     */
    private MCS mcs;

    /**
     * Stores the result.
     */
    private MCSProblem mcsProb;

    /**
     * Will store some information, which will be used later.
     */
    private MCSShadow shadow;

    /**
     * Almost the wanted MCS
     */
    private PseudoMCS pseudo;

    /**
     * Produces SMT-formulas.
     */
    private FormulaFactory<SMTLIBTheoryAtom> factory;

    /**
     * The aborter
     */
    private Abortion aborter;

    /**
     * The SMT engine.
     */
    private SMTEngine smtEngine;

    /**
     * Constructor
     */
    public IDPToMCSConverter() {
        super();
    }

    /**
     * Work on the given obligation.
     *
     * @param obl an IDPProblem
     * @param abortion the aborter
     * @throws AbortionException can be aborted
     * @return some trash ;)
     */
    public MCSProblem convert(final IDPProblem obl, final Abortion abortion)
        throws AbortionException {
        // Initialize:
        this.idp = obl;
        this.idpR = this.idp.getR();
        this.idpP = this.idp.getP();
        this.graph = this.idp.getIdpGraph();
        this.idpEdges = this.graph.getEdges();
        this.predefinedMap = IDPPredefinedMap.DEFAULT_MAP;
        this.shadow = null;
        this.pseudo = null;
        this.mcsProb = null;
        this.mcs = null;
        this.factory = new FullSharingFactory<SMTLIBTheoryAtom>();
        this.iTermRewriter = new ITermRewriter(this.factory);
        this.bTermRewriter = new BTermRewriter(this.factory, this.iTermRewriter);
        this.smtEngine = new YicesEngine();
        this.aborter = abortion;

        this.dumpObligation();

        // Fireworks!
        this.transform();

        return this.mcsProb;
    }

    /**
     * Transforms the IDP into a MCS.
     * @throws AbortionException can be aborted
     */
    private void transform() throws AbortionException {
        // This transformation will run in several stages
        // finally resulting in a MCS.
        // 1. Analyze:
        this.analyze();

        // 2. Transform to numerical normal form (NNF) and create the MCS
        // shadow:
        this.transformToNNF();
        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("idptomcs");
            l.logln("transfomToNNF() generated:\n" + this.shadow.toString());
        }

        // 2. Create the Pseudo MCS
        this.transformToPseudoMCS();
        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("idptomcs");
            l.logln("transformToPseudoMCS() generated:\n" + this.pseudo);
            l.logln("dotString:\n" + this.pseudo.toDOT());
        }

        // 3. Create the MCS
        this.transformToMCS();
        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("idptomcs");
            l.logln("transfromToMCS() generated:\n" + this.mcs);
            //l.logln("dotString:\n" + this.mcs.toDot());
        }

        // 4. Simplify
        this.simplifyMCS();
        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("idptomcs");
            l.logln("simplifyMCS() generated:\n" + this.mcs);
            l.logln("dotString:\n" + this.mcs.toDOT());
        }

        // 5. Fill result in a MCSProblem
        this.toMCSProblem();
    }

    /**
     * Converts the MCS into a MCSProblem.
     */
    private void toMCSProblem() {
        final Set<MCRule> rules = new LinkedHashSet<MCRule>();

        // Rewrite every edge to corresponding a MCOrderingConstraints-object
        for (final Triple<MCSNode, ArrayList<MCSConstraint> , MCSNode> edge : this.mcs.edges) {
            final List<MCSConstraint> constraints = edge.getY();

            final Map<Pair<TRSVariable, TRSVariable>, MCRelation> vpm =
                new LinkedHashMap<Pair<TRSVariable, TRSVariable>, MCRelation>();

            // Rewrite a MCSContraint to a corresponding map entry
            for (final MCSConstraint c : constraints) {
                final Pair<TRSVariable, TRSVariable> p =
                    new Pair<TRSVariable, TRSVariable>(TRSTerm.createVariable(c.left.getName()),
                            TRSTerm.createVariable(c.right.getName()));
                vpm.put(p, c.op.toMCRelation());
            }
            final MCOrderConstraints orderConstraints =
                MCOrderConstraints.createFromVarPairMap(vpm);

            final MCSNode left = edge.getX();
            final MCSNode right = edge.getZ();

            final MCRule rule = MCRule.create(
                    left.toFunctionApplication(),
                    right.toFunctionApplication(),
                    orderConstraints);
            rules.add(rule);
        }

        this.mcsProb = MCSProblem.create(ImmutableCreator.create(rules));
    }

    /**
     * Transform the Pseudo-MCS into a real MCS. This is achieved by inserting
     * new variables representing used constants.
     */
    private void transformToMCS() {
        // 0. Initialize:
        this.mcs = new MCS();

        // 1. Find constants
        final Set<BigInteger> constants = new LinkedHashSet<BigInteger>();
        for (final Triple<MCSNode, ArrayList<AbstractConstraint>, MCSNode> edge : this.pseudo.edges) {
            for (final AbstractConstraint ac : edge.getY()) {
                if (ac instanceof PseudoMCSConstraint) {
                    final PseudoMCSConstraint pseudoCon = (PseudoMCSConstraint) ac;
                    constants.add(pseudoCon.right);
                }
            }
        }

        // 2. Generate new nodes:
        for (final MCSNode node : this.pseudo.nodes) {
            for (final BigInteger c : constants) {
                node.variables.add(MCSVariable.create(c, node.getPostfix()));
            }
            this.mcs.nodes.add(node);
        }

        // 3. Generate new edges:
        for (final Triple<MCSNode, ArrayList<AbstractConstraint>, MCSNode> edge : this.pseudo.edges) {
            final ArrayList<MCSConstraint> newConstraints = new ArrayList<MCSConstraint>();
            for (final AbstractConstraint ac : edge.getY()) {
                if (ac instanceof MCSConstraint) {
                    newConstraints.add((MCSConstraint) ac);
                } else if (ac instanceof PseudoMCSConstraint) {
                    final PseudoMCSConstraint pseudoCon = (PseudoMCSConstraint) ac;
                    final MCSConstraint newConstraint = new MCSConstraint(
                            pseudoCon.left, pseudoCon.op, MCSVariable.create(
                                    pseudoCon.right, edge.getX().getPostfix()));
                    newConstraints.add(newConstraint);
                } else {
                    assert false;
                }
            }
            for (final BigInteger c1 : constants) {
                for (final BigInteger c2 : constants) {
                    if (c1.compareTo(c2) < 0) {
                        final MCSConstraint newConstraint = new MCSConstraint(
                                MCSVariable.create(c1, edge.getX().getPostfix()),
                                MCSOperator.MCS_L, MCSVariable.create(
                                        c2,
                                        edge.getX().getPostfix()));
                        newConstraints.add(newConstraint);
                    }
                }
                final MCSConstraint newConstraint = new MCSConstraint(
                        MCSVariable.create(c1, edge.getX().getPostfix()),
                        MCSOperator.MCS_EQ, MCSVariable.create(c1, edge.getZ()
                                .getPostfix()));
                newConstraints.add(newConstraint);
            }

            final Triple<MCSNode, ArrayList<MCSConstraint>, MCSNode> newEdge =
                new Triple<MCSNode, ArrayList<MCSConstraint>, MCSNode>(
                    edge.getX(), newConstraints, edge.getZ());
            this.mcs.edges.add(newEdge);
        }

    }

    /**
     * Simplifies the MCS. Replaces every MCS_L (MCS_LE) by MCS_G (MCS_GE).
     * Removes some unneeded constraints.
     */
    private void simplifyMCS() {
        // TODO: My knowledge graph toy is probably better than MCSConstraint.implies()!
        // 1. Simplify constraints:
        for (final Triple<MCSNode, ArrayList<MCSConstraint>, MCSNode> edge : this.mcs.edges) {
            final ArrayList<MCSConstraint> constraints = new ArrayList<MCSConstraint>(edge.getY().size());
            // Turn y < x into x > y and y <= x into x >= y.
            // Furthermore turn (x >= y && y >= x) into x = y and (x >= y && x = y) into x = y.
            for (final MCSConstraint c : edge.getY()) {
                final MCSConstraint con = c.normalize();

                boolean isTriviallyImplied = false;
                for (final MCSConstraint old : constraints) {
                    if (old.implies(con)) {
                        isTriviallyImplied = true;
                        break;
                    }
                }

                if (!isTriviallyImplied) {
                    if (con.op.equals(MCSOperator.MCS_EQ)) {
                        constraints.remove(new MCSConstraint(con.left, MCSOperator.MCS_GE, con.right));
                        constraints.remove(new MCSConstraint(con.right, MCSOperator.MCS_GE, con.left));
                        constraints.add(con);
                    } else if (con.op.equals(MCSOperator.MCS_GE)) {
                        final MCSConstraint test = new MCSConstraint(
                                con.right, MCSOperator.MCS_GE, con.left);
                        if (constraints.contains(test)) {
                            constraints.remove(test);
                            constraints.add(new MCSConstraint(con.left, MCSOperator.MCS_EQ, con.right));
                        } else {
                            constraints.add(con);
                        }
                    } else if (con.op.equals(MCSOperator.MCS_G)) {
                        constraints.add(con);
                    } else {
                        // This should not happen, since [con] is normalized.
                        assert false;
                        constraints.add(con);
                    }
                }
            }
            edge.setY(constraints);
        }

        // 2. Remove variable not occurring in constraints:
        final LinkedHashSet<MCSVariable> occurringVariables = new LinkedHashSet<MCSVariable>();
        for (final Triple<MCSNode, ArrayList<MCSConstraint>, MCSNode> edge : this.mcs.edges) {
            for (final MCSConstraint c : edge.getY()) {
                occurringVariables.add(c.left);
                occurringVariables.add(c.right);
            }
        }
        for (final MCSNode node : this.mcs.nodes) {
            node.variables.retainAll(occurringVariables);
        }
    }

    /**
     * Pass
     */
    private void analyze() {
        // Pass
        // TODO: Implement check, whether or not rewriting ITPFs can
        // be used for constraint generation, if R is not empty.
    }

    /**
     * Searches for constants.
     *
     * @param constantList constants will be filled in there
     */
    private void searchConstants(final LinkedHashSet<BigInteger> constantList) {
        this.searchConstants(constantList, this.idpR);
        this.searchConstants(constantList, this.idpP);
        this.searchConstants(constantList, this.shadow.nodes);
        for (final IdpEdge edge : this.idpEdges) {
            this.searchConstants(constantList, edge.getItpf());
        }
    }

    /**
     * Searches for constants.
     *
     * @param constantList constants will be filled in there
     * @param itpf where to search.
     */
    private void searchConstants(final LinkedHashSet<BigInteger> constantList,
            final Itpf itpf) {
        for (final FunctionSymbol sym : itpf.getFunctionSymbols()) {
            if (this.predefinedMap.isInt(sym, DomainFactory.INTEGERS)) {
                constantList.add(this.predefinedMap.getInt(sym,
                        DomainFactory.INTEGERS));
            }
        }
    }

    /**
     * Searches for constants.
     *
     * @param constantList constants will be filled in there
     * @param ruleSet where to search.
     */
    private void searchConstants(final LinkedHashSet<BigInteger> constantList,
            final Set<GeneralizedRule> ruleSet) {
        for (final GeneralizedRule gr : ruleSet) {
            this.searchConstants(constantList, gr.getLeft());
            this.searchConstants(constantList, gr.getRight());
        }
    }

    /**
     * Searches for constants.
     *
     * @param constantList constants will be filled in there
     * @param t where to search.
     */
    private void searchConstants(final LinkedHashSet<BigInteger> constantList,
            final TRSTerm t) {
        if (!t.isVariable()) {
            final TRSFunctionApplication f = (TRSFunctionApplication) t;
            if (f.isConstant()) {
                final FunctionSymbol sym = f.getRootSymbol();
                if (this.predefinedMap.isInt(sym, DomainFactory.INTEGERS)) {
                    constantList.add(this.predefinedMap.getInt(sym,
                            DomainFactory.INTEGERS));
                }
            } else {
                for (final TRSTerm arg : f.getArguments()) {
                    this.searchConstants(constantList, arg);
                }
            }
        }
    }

    /**
     * Infers constraints in "MCS-form" and inserts them into the current edge.
     *
     * @param gr the current transition
     * @param edge the current edge
     * @param itpf optional ITPF
     * @param constants set of interesting constants
     * @throws AbortionException can be aborted
     */
    private void inferConstraints(
            final GeneralizedRule gr,
            final Triple<MCSNode, ArrayList<AbstractConstraint>, MCSNode> edge,
            final Itpf itpf,
            final Set<BigInteger> constants) throws AbortionException {
        // 1. Initialize:
        final KnowledgeGraph kg = new KnowledgeGraph();
        final Set<RulePosition> grrps =
            RulePosition.getDirectRulePositions(gr);

        // 2. Try to infer constraints for each pair of rule positions:
        this.inferRulePositionConstraints(gr, edge, itpf, kg, grrps);

        // 3. Try to infer constraints using constants:
        this.inferConstantConstraints(gr, edge, itpf, constants, kg, grrps);
    }

    /**
     * Infers constraint using constants.
     *
     * @param gr the current rule
     * @param edge the current edge
     * @param itpf optional ITPF
     * @param constants set of interesting constants
     * @param kg current knowledge graph
     * @param grrps rule positions
     * @throws AbortionException can be aborted
     */
    private void inferConstantConstraints(final GeneralizedRule gr,
            final Triple<MCSNode, ArrayList<AbstractConstraint>, MCSNode> edge,
            final Itpf itpf, final Set<BigInteger> constants,
            final KnowledgeGraph kg, final Set<RulePosition> grrps)
            throws AbortionException {
        if (constants == null) {
            return;
        }
        for (final RulePosition i : grrps) {
            // Compare each position with an interesting constant:
            for (final BigInteger bi : constants) {
                final MCSVariable vi = this.getCorrespondingMCSVariable(edge, i);
                final MCSVariable vj = MCSVariable.create(bi);
                if (kg.isImplied(new MCSConstraint(vi, MCSOperator.MCS_LE, vj))
                        || !this.checkSat(gr, i, MCSOperator.MCS_G, bi, itpf)) {
                    if (kg.isImplied(new MCSConstraint(vi, MCSOperator.MCS_L, vj))
                            || !this.checkSat(gr, i, MCSOperator.MCS_GE, bi, itpf)) {
                        this.insertConstraint(i, edge, bi, MCSOperator.MCS_L, kg);
                    } else {
                        this.insertConstraint(i, edge, bi,
                                MCSOperator.MCS_LE, kg);
                    }
                } else if (kg.isImplied(new MCSConstraint(vi, MCSOperator.MCS_GE, vj))
                               || !this.checkSat(gr, i, MCSOperator.MCS_L, bi, itpf)) {
                    if (kg.isImplied(new MCSConstraint(vi, MCSOperator.MCS_G, vj))
                            || !this.checkSat(gr, i, MCSOperator.MCS_LE, bi, itpf)) {
                        this.insertConstraint(i, edge, bi, MCSOperator.MCS_G, kg);
                    } else {
                        this.insertConstraint(i, edge, bi, MCSOperator.MCS_GE, kg);
                    }
                }
            }
        }
    }

    /**
     * Inspects each pair of rule positions.
     *
     * @param gr the current rule
     * @param edge the current edge
     * @param itpf optional ITPF [can also be null]
     * @param kg the current knowledge graph
     * @param grrps rule positions
     * @throws AbortionException can be aborted
     */
    private void inferRulePositionConstraints(final GeneralizedRule gr,
            final Triple<MCSNode, ArrayList<AbstractConstraint>, MCSNode> edge,
            final Itpf itpf, final KnowledgeGraph kg,
            final Set<RulePosition> grrps) throws AbortionException {
        for (final RulePosition i : grrps) {
            // Compare each pair of positions
            for (final RulePosition j : grrps) {
                if (i.equals(j)) {
                    continue;
                }
                final MCSVariable vi = this.getCorrespondingMCSVariable(edge, i);
                final MCSVariable vj = this.getCorrespondingMCSVariable(edge, j);
                if (kg.isImplied(new MCSConstraint(vi, MCSOperator.MCS_LE, vj))
                        || !this.checkSat(gr, i, MCSOperator.MCS_G, j, itpf)) {

                    if (kg.isImplied(new MCSConstraint(vi, MCSOperator.MCS_L, vj))
                            || !this.checkSat(gr, i, MCSOperator.MCS_GE, j, itpf)) {
                        this.insertConstraint(i, edge, j, MCSOperator.MCS_L, kg);
                    } else {
                        this.insertConstraint(i, edge, j, MCSOperator.MCS_LE, kg);
                    }
                }
            }
        }
    }

    /**
     * This will transform a MCS Shadow into a pseudo MCS using the SMT-Solver
     * to generate some constraints in "MCS-Form".
     *
     * @throws AbortionException can be aborted
     */
    private void transformToPseudoMCS() throws AbortionException {
        // 0. Initialize:
        this.pseudo = new PseudoMCS();
        final LinkedHashMap<GeneralizedRule, MCSNode> mapLeft =
            new LinkedHashMap<GeneralizedRule, MCSNode>();
        final LinkedHashMap<GeneralizedRule, MCSNode> mapRight =
            new LinkedHashMap<GeneralizedRule, MCSNode>();

        // 1. Find interesting constants:
        final LinkedHashSet<BigInteger> constants = new LinkedHashSet<BigInteger>();
        this.searchConstants(constants);

        // 2. Use the rules to create nodes + edges:
        for (final GeneralizedRule rule : this.shadow.nodes) {
            final TRSFunctionApplication leftFunc = rule.getLeft();
            final TRSTerm rightTerm = rule.getRight();
            assert rightTerm instanceof TRSFunctionApplication;
            final TRSFunctionApplication rightFunc = (TRSFunctionApplication) rightTerm;

            final MCSNode leftNode = this.createMCSNode(leftFunc);
            final MCSNode rightNode = this.createMCSNode(rightFunc);

            this.pseudo.nodes.add(leftNode);
            this.pseudo.nodes.add(rightNode);

            mapLeft.put(rule, leftNode);
            mapRight.put(rule, rightNode);

            final Triple<MCSNode, ArrayList<AbstractConstraint>, MCSNode> newEdge =
                new Triple<MCSNode, ArrayList<AbstractConstraint>, MCSNode>(
                    leftNode, new ArrayList<AbstractConstraint>(), rightNode);
            this.pseudo.edges.add(newEdge);

            this.inferConstraints(rule, newEdge, null, constants);
        }

        // 3. Use ITPFs to create additional edges:
        for (final Triple<GeneralizedRule, Itpf, GeneralizedRule> triple : this.shadow.edges) {
            // If we have l1 -> r1 and l2 -> r2, which are connected in the
            // IDPGraph, then we should connect r1 with l2.

            final MCSNode left = mapRight.get(triple.getX());
            final Itpf itpf = triple.getY();
            final MCSNode right = mapLeft.get(triple.getZ());

            final ArrayList<AbstractConstraint> constraints = new ArrayList<AbstractConstraint>();

            final Triple<MCSNode, ArrayList<AbstractConstraint>, MCSNode> edge =
                new Triple<MCSNode, ArrayList<AbstractConstraint>, MCSNode>(
                    left, constraints, right);
            this.pseudo.edges.add(edge);

            // Get constraints from the ITPF:
            final GeneralizedRule gr = GeneralizedRule.create(
                    (TRSFunctionApplication) triple.getX().getRight(),
                    triple.getZ().getLeft());
            this.inferConstraints(gr, edge, itpf, constants);
        }
    }

    /**
     * Translate the ITPF into some constraints.
     *
     * @param itpf a conjunction of ITPFs without disjunctions.
     * @param formulae to be filled by constraints.
     */
    private void getItpfConstraints(final Itpf itpf,
            final List<Formula<SMTLIBTheoryAtom>> formulae) {
        // TODO: Rework this to include some rewriting ITPFs using non empty R.
        if (itpf.isAnd()) {
            final ItpfAnd itAnd = (ItpfAnd) itpf;
            for (final Itpf child : itAnd.getChildren()) {
                this.getItpfConstraints(child, formulae);
            }
        } else if (itpf.isOr()) {
            // This is impossible, since the DNF was split into its clauses.
            assert false;
        } else if (itpf instanceof ItpfItp) {
            final ItpfItp itp = (ItpfItp) itpf;
            final TRSTerm left = itp.getL();
            final TRSTerm right = itp.getR();
            final ItpRelation rel = itp.getRelation();
            if (rel.equals(ItpRelation.TO_TRANS)) {
                // TODO: Implement a better a way of comparing to symbol TRUE
                if (right.isConstant() && "TRUE".equals(right.getName())
                        && left instanceof TRSFunctionApplication) {
                    formulae.add(this.bTermRewriter.rewrite((TRSFunctionApplication) left));
                } else {
                    if (this.idpR.isEmpty()) {
                        // Since R is empty, we can gain a lot of knowledge:
                        // Get MGU of these terms
                        final TRSSubstitution sub = left.getMGU(right);
                        if (sub == null) {
                            return;
                        }

                        // For each instantiation ..
                        for (final TRSVariable v : sub.getVariables()) {
                            // .. create representing formulas.
                            final TRSTerm t = v.applySubstitution(sub);
                            final Pair<SMTLIBIntVariable, Formula<SMTLIBTheoryAtom>> res =
                                this.iTermRewriter.rewrite(this.convertTerm(t));
                            final SMTLIBTheoryAtom preciousAtom =
                                SMTLIBIntEquals.create(res.getKey(),
                                        SMTLIBIntVariable.create(v.getName()));
                            final Formula<SMTLIBTheoryAtom> result =
                                this.factory.buildAnd(res.getValue(),
                                        this.factory.buildTheoryAtom(preciousAtom));
                            formulae.add(result);
                        }
                    }
                }
            }
        }
        // TODO: Extend this to handle more ITPFs.
    }

    /**
     * Returns the corresponding MCSVariable
     * @param edge the current edge
     * @param i the position
     * @return the corresponding MCSVariable
     */
    private MCSVariable getCorrespondingMCSVariable(
            final Triple<MCSNode, ArrayList<AbstractConstraint>, MCSNode> edge,
            final RulePosition i) {
        final MCSNode node;
        if (i.isLeft()) {
            node = edge.getX();
        } else {
            node = edge.getZ();
        }
        return node.variables.get(i.getPosition().firstIndex());
    }

    /**
     * Inserts a constraint.
     *
     * @param i first position
     * @param edge current edge
     * @param j second position
     * @param op an MCSOperator
     * @param kg current knowledge graph
     */
    private void insertConstraint(final RulePosition i,
            final Triple<MCSNode, ArrayList<AbstractConstraint>, MCSNode> edge,
            final RulePosition j, final MCSOperator op,
            final KnowledgeGraph kg) {
        final MCSVariable var1 = this.getCorrespondingMCSVariable(edge, i);
        final MCSVariable var2 = this.getCorrespondingMCSVariable(edge, j);
        final MCSConstraint constraint = new MCSConstraint(var1, op, var2);
        edge.getY().add(constraint);
        if (kg != null) {
            kg.insertConstraint(constraint);
        }
    }

    /**
     * Inserts a constraint.
     *
     * @param i position
     * @param edge current edge
     * @param b constant
     * @param op an MCSOperator
     * @param kg current knowledge graph
     */
    private void insertConstraint(final RulePosition i,
            final Triple<MCSNode, ArrayList<AbstractConstraint>, MCSNode> edge,
            final BigInteger b, final MCSOperator op,
            final KnowledgeGraph kg) {
        MCSNode iNode = null;
        if (i.isLeft()) {
            iNode = edge.getX();
        } else {
            iNode = edge.getZ();
        }
        final MCSVariable var1 = iNode.variables.get(
                i.getPosition().firstIndex());
        final PseudoMCSConstraint constraint = new PseudoMCSConstraint(var1,
                op, b);
        edge.getY().add(constraint);
        if (kg != null) {
            kg.insertConstraint(constraint);
        }
    }

    /**
     * Returns true IFF the SMT Solver says, that [i] [op] [j] is unsatisfiable.
     *
     * @param rule rule containing the current transition.
     * @param i first position
     * @param op the relation symbol
     * @param j second position
     * @param itpf additionally an itpf [can also be null]
     * @return boolean
     * @throws AbortionException can be aborted
     */
    private boolean checkSat(final GeneralizedRule rule, final RulePosition i,
            final MCSOperator op, final RulePosition j, final Itpf itpf) throws AbortionException {
        // 1. Initialize:
        final LinkedList<Formula<SMTLIBTheoryAtom>> formulae =
            new LinkedList<Formula<SMTLIBTheoryAtom>>();
        SMTLIBIntVariable leftVar = null;
        SMTLIBIntVariable rightVar = null;

        // 2. Get knowledge from the given ITPF:
        if (itpf != null) {
            this.getItpfConstraints(itpf, formulae);
        }

        // 3. Rewrite the given position to formulas:
        final TRSTerm leftSub = i.applyToRule(rule);
        if (leftSub != null && this.resultsInteger(leftSub)) {
            leftVar = this.iTermRewriter.rewrite(leftSub, formulae);
        }
        final TRSTerm rightSub = j.applyToRule(rule);
        if (rightSub != null && this.resultsInteger(rightSub)) {
            rightVar = this.iTermRewriter.rewrite(rightSub, formulae);
        }

        // 4. Ask the SMT-Solver:
        return this.askSMTSolver(op, formulae, leftVar, rightVar);
    }

    /**
     * Asks the SMT-Solver whether or not
     * [leftVar] [op] [rightVar] AND conjunction of [theory]
     * is unsatisfiable.
     *
     * @param op a MCS-Relationsymbol
     * @param theory list of axioms
     * @param leftVar a SMT-Variable
     * @param rightVar another SMT-Variable
     * @return false IFF the SMT-Solver says UNSAT
     * @throws AbortionException can be aborted
     */
    private boolean askSMTSolver(final MCSOperator op,
            final LinkedList<Formula<SMTLIBTheoryAtom>> theory,
            final SMTLIBIntVariable leftVar, final SMTLIBIntVariable rightVar)
            throws AbortionException {
        // 4. If we can make use of these position ..
        if (leftVar != null && rightVar != null) {
            // .. then we should build the requested formula and ask the SMT-Solver!
            Formula<SMTLIBTheoryAtom> toAsk = this.factory.buildAnd(theory);
            SMTLIBTheoryAtom preciousAtom = null;
            switch (op) {
            case MCS_GE:
                preciousAtom = SMTLIBIntGE.create(leftVar, rightVar);
                break;
            case MCS_G:
                preciousAtom = SMTLIBIntGT.create(leftVar, rightVar);
                break;
            case MCS_EQ:
                preciousAtom = SMTLIBIntEquals.create(leftVar, rightVar);
                break;
            case MCS_L:
                preciousAtom = SMTLIBIntLT.create(leftVar, rightVar);
                break;
            case MCS_LE:
                preciousAtom = SMTLIBIntLE.create(leftVar, rightVar);
                break;
            default:
                assert false;
                break;
            }
            toAsk = this.factory.buildAnd(this.factory.buildTheoryAtom(preciousAtom), toAsk);

            // Ask the SMT-Solver:
            YNM res;
            try {
                res = this.smtEngine.satisfiable(Collections.singletonList(toAsk), SMTLogic.QF_LIA, this.aborter);
            } catch (final WrongLogicException e) {
                System.err.println("Solver error: " + e.getErrorMessage());
                res = YNM.MAYBE;
            }
            // Return false IFF SMT-Solver says UNSAT.
            return res != YNM.NO;

        } else {
            // Comparing boolean values with anything always yield true.
            return true;
        }
    }

    /**
     * Returns true IFF the SMT Solver says, that [i] [op] [j] is unsatisfiable.
     *
     * @param rule rule containing the current transition.
     * @param i position
     * @param op the relation symbol
     * @param j constant
     * @param itpf additional ITPF [can also be null]
     * @return boolean
     * @throws AbortionException can be aborted
     */
    private boolean checkSat(final GeneralizedRule rule, final RulePosition i,
            final MCSOperator op, final BigInteger j, final Itpf itpf) throws AbortionException {
        // 1. Initialize:
        final LinkedList<Formula<SMTLIBTheoryAtom>> formulae =
            new LinkedList<Formula<SMTLIBTheoryAtom>>();
        SMTLIBIntVariable leftVar = null;
        SMTLIBIntVariable rightVar = null;

        // 2. Get knowledge from the given ITPF:
        if (itpf != null) {
            this.getItpfConstraints(itpf, formulae);
        }

        // 3. Create SMT-Formula representing the right constant:
        rightVar = SMTLIBIntVariable.create(IDPToMCSUtility.getFreshName());
        formulae.add(this.factory.buildTheoryAtom(SMTLIBIntEquals.create(
                SMTLIBIntConstant.create(j), rightVar)));

        // 4. Rewrite left hand side:
        final TRSTerm leftSub = i.applyToRule(rule);
        if (leftSub != null && this.resultsInteger(leftSub)) {
            leftVar = this.iTermRewriter.rewrite(leftSub, formulae);
        }

        // 5. Ask the SMT Solver:
        return this.askSMTSolver(op, formulae, leftVar, rightVar);
    }

    /**
     * @param t a Term using only predefined symbols.
     * @return true IFF a interpretation would yield an integer.
     */
    private boolean resultsInteger(final TRSTerm t) {
        assert t != null;
        if (t instanceof TRSFunctionApplication) {
            final FunctionSymbol sym =
                ((TRSFunctionApplication) t).getRootSymbol();
            // TODO: Is that all? Or is there a better way to do it?
            return (this.predefinedMap.isInt(sym, DomainFactory.INTEGERS)
                    || this.predefinedMap.isAdd(sym)
                    || this.predefinedMap.isSub(sym)
                    || this.predefinedMap.isMul(sym)
                    || this.predefinedMap.isDivOrMod(sym));
        }
        return true;
    }

    /**
     * Turns a function application into a MCS-Node.
     *
     * @param func a function application
     * @return a MCSNode.
     */
    private MCSNode createMCSNode(final TRSFunctionApplication func) {
        final MCSNode result = new MCSNode();
        for (int i = 0; i < func.getArguments().size(); i++) {
            result.variables.add(MCSVariable.create());
        }
        return result;
    }

    /**
     * This will replace some function symbol by numerical construction.
     * Furthermore a MCS frame graph will be created.
     */
    private void transformToNNF() {
        // 1. Initialize:
        this.shadow = new MCSShadow();
        final LinkedHashMap<Node, GeneralizedRule> map = new LinkedHashMap<Node, GeneralizedRule>();

        // 2. Create nodes:
        for (final Node node : this.graph.getNodes()) {
            final GeneralizedRule rule = node.getRule();

            final TRSFunctionApplication left = rule.getLeft();
            final TRSTerm rightTerm = rule.getRight();
            assert !rightTerm.isVariable();
            final TRSFunctionApplication right = (TRSFunctionApplication) rightTerm;

            final TRSFunctionApplication newLeft = this.convertTermToNNF(left);
            final TRSFunctionApplication newRight = this.convertTermToNNF(right);

            final GeneralizedRule newRule = GeneralizedRule.create(newLeft,
                    newRight);
            map.put(node, newRule);
            this.shadow.nodes.add(newRule);
        }

        // 3. Create edges:
        for (final IdpEdge edge : this.graph.getEdges()) {
            final Node from = edge.getFrom();
            final Node to = edge.getTo();

            final Itpf itpf = edge.getItpf();
            final GeneralizedRule fromRule = map.get(from);
            GeneralizedRule toRule = map.get(to);

            if (from.equals(to)) {
                // If a IDP edge is a backstrap, then the variable names get some single quotes:
                toRule = this.getSingleQuotedRule(toRule);
            }

            final LinkedList<Itpf> itpfs = this.handleItpf(itpf);
            for (final Itpf newItpf : itpfs) {
                final Triple<GeneralizedRule, Itpf, GeneralizedRule> shadowEdge =
                    new Triple<GeneralizedRule, Itpf, GeneralizedRule>(
                        fromRule, newItpf, toRule);
                this.shadow.edges.add(shadowEdge);
            }
        }
    }

    /**
     * Changes variables names: varname -> varname'
     * @param rule a rule
     * @return renamed rule
     */
    private GeneralizedRule getSingleQuotedRule(final GeneralizedRule rule) {
        final TRSTerm left = this.getSingleQuotedTerm(rule.getLeft());
        final TRSTerm right = this.getSingleQuotedTerm(rule.getRight());

        assert left instanceof TRSFunctionApplication;

        return GeneralizedRule.create((TRSFunctionApplication) left, right);
    }


    /**
     * Changes variables names: varname -> varname'
     * @param t a term
     * @return renamed term
     */
    private TRSTerm getSingleQuotedTerm(final TRSTerm t) {
        final Set<TRSVariable> vars = t.getVariables();
        final LinkedHashMap<TRSVariable, TRSVariable> map = new LinkedHashMap<TRSVariable, TRSVariable>(
                vars.size());
        for (final TRSVariable var : vars) {
            final TRSVariable newVar = TRSTerm.createVariable(var.getName() + "'");
            map.put(var, newVar);
        }
        final TRSSubstitution sub = TRSSubstitution.create(
                ImmutableCreator.create(map));
        return t.applySubstitution(sub);
    }

    /**
     * Filter a conjunction of ITPFs.
     *
     * @param itpf a conjunction of ITPFs.
     * @return filtered ITPF
     */
    private Itpf filterItpfClause(final Itpf itpf) {
        // TODO: Use as much ITPFs as possible.
        if (itpf.isAnd()) {
            final ItpfAnd itAnd = (ItpfAnd) itpf;
            final LinkedHashSet<Itpf> newChildren = new LinkedHashSet<Itpf>();
            for (final Itpf child : itAnd.getChildren()) {
                final Itpf newItpf = this.filterItpfClause(child);
                if (newItpf != null) {
                    newChildren.add(newItpf);
                }
            }
            final ImmutableSet<Itpf> immuNewChildren =
                    ImmutableCreator.create(newChildren);
            return ItpfAnd.create(immuNewChildren);
        } else if (itpf.isAtom()) {
            final ItpfAtom atom = (ItpfAtom) itpf;
            if (atom instanceof ItpfItp) {
                return itpf;
            }
            // Drop:
            return null;
        }
        // Drop:
        return null;
    }

    /**
     * Partitions an ITPF into a list of filtered ITPF conjunctions.
     *
     * @param itpf an ITPF
     * @return a List of ITPFs
     */
    private LinkedList<Itpf> handleItpf(final Itpf itpf) {
        final LinkedList<Itpf> clauses = new LinkedList<Itpf>();
        this.getClauses(itpf.normalize().toDnf(), clauses);

        final LinkedList<Itpf> result = new LinkedList<Itpf>();

        for (final Itpf clause : clauses) {
            result.add(this.filterItpfClause(clause));
        }

        return result;
    }

    /**
     * Partitions a DNF-ITPF into a list of clauses.
     *
     * @param dnfItpf a ITPF in DNF.
     * @param resultList list to fill in clauses.
     */
    private void getClauses(final Itpf dnfItpf,
            final LinkedList<Itpf> resultList) {
        if (dnfItpf.isOr()) {
            final ItpfOr itOr = (ItpfOr) dnfItpf;
            for (final Itpf child : itOr.getChildren()) {
                this.getClauses(child, resultList);
            }
        } else {
            resultList.add(dnfItpf);
        }
    }

    /**
     * Converts a Term into its numerical normal form.
     *
     * @param func a function application.
     * @return a function application.
     */
    private TRSFunctionApplication convertTermToNNF(final TRSFunctionApplication func) {
        final ArrayList<TRSTerm> arguments = new ArrayList<TRSTerm>();
        for (final TRSTerm argument : func.getArguments()) {
            arguments.add(this.convertTerm(argument));
        }

        final TRSFunctionApplication result =
            TRSTerm.createFunctionApplication(func.getRootSymbol(),
                        ImmutableCreator.create(arguments));
        return result;
    }

    /**
     * Converts a Term into its numerical normal form.
     *
     * @param arg a Term.
     * @return a converted term.
     */
    private TRSTerm convertTerm(final TRSTerm arg) {
        if (arg.isVariable()) {
            return arg;
        } else {
            final TRSFunctionApplication func = (TRSFunctionApplication) arg;
            final FunctionSymbol sym = func.getRootSymbol();

            // TODO: Find out the best way to compare symbols.
            if ("java.lang.Object".equals(sym.getName())) {
                int size = 0;
                TRSTerm current = arg;
                while (!current.isVariable()
                       && ((TRSFunctionApplication) current).getArguments().size() == 1) {
                    size++;
                    current = ((TRSFunctionApplication) current).getArgument(0);
                }
                TRSTerm result = IDPToMCSUtility.createIntegerTerm(size);

                final ArrayList<TRSTerm> newArgs;
                if (current.isVariable()) {
                    newArgs = new ArrayList<TRSTerm>(1);
                    newArgs.add(current);
                } else {
                    final TRSFunctionApplication currentFunc = (TRSFunctionApplication) current;
                    final ImmutableList<TRSTerm> arguments = currentFunc.getArguments();
                    newArgs = new ArrayList<TRSTerm>(arguments.size());
                    for (final TRSTerm sub : arguments) {
                        newArgs.add(this.convertTerm(sub));
                    }
                }
                result =
                    IDPToMCSUtility.createAdditionTerm(
                        result,
                        TRSTerm.createFunctionApplication(
                            FunctionSymbol.create("PMAX", newArgs.size()),
                            ImmutableCreator.create(newArgs)
                        )
                    );
                return result;
            } else if (this.predefinedMap.contains(sym.getName())) {
                return arg;
            } else {
                TRSTerm result = IDPToMCSUtility.createIntegerTerm(1);
                for (final TRSTerm sub : func.getArguments()) {
                    result = IDPToMCSUtility.createAdditionTerm(result,
                            this.convertTerm(sub));
                }
                return result;
            }
        }
    }

    /**
     * Only used for debugging purposes.
     */
    private void dumpObligation() {
        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("idptomcs");
            l.logln("Given obligation:");
            l.logln(this.idp.toString());
            l.logln("------------------------------");
        }
    }
}
