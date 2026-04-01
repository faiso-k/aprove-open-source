package aprove.input.Programs.impact.GTP;

import java.util.*;

import aprove.input.Programs.SMTLIB.Exceptions.*;
import aprove.input.Programs.impact.GTP.nodes.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.ProgramGraph.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.ProgramGraph.Locations.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.Relation.TermRelation.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.TransitionPair.TermTransitionPair.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.SAT.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;



/**
 * GO-TO program, merely a list of commands (nodes.CommandNode)
 * @author marinag
 *
 */
public class GtpProgram  {

    final ImmutableList<CommandNode> commands;

    public GtpProgram(final ArrayList<CommandNode> commands) {
        this.commands = ImmutableCreator.create(commands);
    }

    private static List<Integer> createIds(final int id, final int subId) {
        final List<Integer> list = new ArrayList<>();
        list.add(id);
        list.add(subId);
        return list;
    }

    private static List<CommandNode> addNdtAssign(final List<CommandNode> commands) {
        final List<CommandNode> result = new LinkedList<>(commands);

        for (int i = 0, j = 0; i < commands.size(); i++) {
            final CommandNode command = commands.get(i);
            BooleanExpressionNode exp = null;
            if (command instanceof AssignCommandNode) {
                exp = ((AssignCommandNode) command).getAssignedExpression();
            } else if (command instanceof ConditionalBranchCommandNode) {
                exp = ((ConditionalBranchCommandNode) command).getCondition();
            }



            if (exp != null) {

                String label = command.getLabel();
                for (final VariableNode var : exp.getNonDetVariables()) {
                    final CommandNode assign =
                        new AssignCommandNode("PREF", command.getLine(), command.getPos(), label, var, null);
                    label = null;
                    command.setLabel(null);

                    result.add(i + j, assign);
                    j++;
                }
            }

        }
        return result;
    }

    private static Map<String, CommandNode> getLabelMap(final List<CommandNode> commands) {
        final Map<String, CommandNode> result = new HashMap<String, CommandNode>();

        for (final CommandNode command : commands) {
            if (command.getLabel() != null) {
                result.put(command.getLabel(), command);
            }
        }
        return result;
    }

    private static Map<String, Set<CommandNode>> getFunctionReturn(final List<CommandNode> commands) {
        final Map<String, Set<CommandNode>> result = new HashMap<>();

        for (int i = 0; i < commands.size() - 1; i++) {
            final CommandNode command = commands.get(i);

            if (command instanceof CallCommandNode) {
                final String id = ((CallCommandNode) command).getCallId();

                if (!result.containsKey(id)) {
                    result.put(id, new HashSet<CommandNode>());
                }
                result.get(id).add(commands.get(i + 1));
            }

        }
        return result;
    }

    private static Map<CommandNode, Location> getLocationMap(final List<CommandNode> commands) {
        final Map<CommandNode, Location> result = new HashMap<>();

        int j = 0;
        final int i = 1;

        for (final CommandNode command : commands) {
            final int id = j++;
            Location loc = null;

            if (command instanceof CallCommandNode) {
                loc = new CallLocation(id, ((CallCommandNode) command).getFunction());
            } else if (command instanceof ReturnCommandNode) {
                loc = new ReturnLocation(id);
            } else if (command instanceof AssignCommandNode) {
                final NumericExpressionNode exp = ((AssignCommandNode) command).getAssignedExpression();
                final String var = ((AssignCommandNode) command).getVariable().toString();

                final Map<String, TRSTerm> assignMap = new HashMap<>();
                assignMap.put(var, exp == null ? null : exp.toTerm());

                final Set<String> globals = new HashSet<>();

                if (((AssignCommandNode) command).getVariable().isGlobal()) {
                    globals.add(var);
                }

                loc = new Location(id);
            } else if (command instanceof PushCommandNode) {
                final VariableNode exp = ((PushCommandNode) command).getVariable();
                loc = new PushLocation(id, exp.toString());
            } else if (command instanceof PopCommandNode) {
                loc = new PopLocation(id, ((PopCommandNode) command).getVariable().toString());
            } else if (command instanceof AbortCommandNode) {
                loc = new AbortLocation(id);
            } else {
                loc = new Location(id);
            }

            result.put(command, loc);
        }

        return result;
    }

    private static Set<Edge<TermTransitionPairsSet, LocationID>> getEdges(
        final List<CommandNode> commands,
        final Map<CommandNode, Location> locationMap,
        final Map<String, CommandNode> labelMap,
        final Map<String, Set<CommandNode>> functionReturn)
        {
        final Abortion aborter = AbortionFactory.create();
        final Set<Edge<TermTransitionPairsSet, LocationID>> edges = new HashSet<>();

        final Set<String> variables = new HashSet<>();

        for (int i = 0; i < commands.size(); i++) {
            final CommandNode command = commands.get(i);

            if (command instanceof AssignCommandNode) {
                variables.add(((AssignCommandNode) command).getVariable().toString());

                if (((AssignCommandNode) command).getAssignedExpression() != null) {
                    variables.addAll(((AssignCommandNode) command).getAssignedExpression().getVariableNames());
                }
            } else if (command instanceof ConditionalBranchCommandNode) {
                variables.addAll(((ConditionalBranchCommandNode) command).getCondition().getVariableNames());
            }
        }

        final ArrayList<String> varList = new ArrayList<>(variables);

        final TermRelation idRel = TermRelation.createIdentity(varList);



        for (int i = 0; i < commands.size(); i++) {
            final CommandNode command = commands.get(i);

            if (command instanceof AssignCommandNode) {
                final List<Pair<TRSVariable, TRSTerm>> currRelMap = new ArrayList<>();

                final String var = ((AssignCommandNode) command).getVariable().toString();
                final TRSTerm value =
                    ((AssignCommandNode) command).getAssignedExpression() == null
                    ? null
                        : ((AssignCommandNode) command).getAssignedExpression().toTerm();

                for (final String vId : varList) {
                    final TRSVariable variable = TRSTerm.createVariable(vId);
                    if (vId.equals(var)) {
                        currRelMap.add(new Pair<>(variable, value));
                    } else {
                        currRelMap.add(new Pair<TRSVariable, TRSTerm>(variable, variable));
                    }
                }


                final TermRelation relation = TermRelation.createRelation(currRelMap);

                edges.add(new Edge<TermTransitionPairsSet, LocationID>(locationMap.get(command), locationMap
                    .get(commands.get(i + 1)), TermTransitionPairsSet.create(new TermTransitionPair(
                        TermTools.TRUE,
                        relation))));

            } else if (command instanceof ReturnCommandNode) {

                final String function = ((ReturnCommandNode) command).getFunction();

                if (functionReturn.containsKey(function)) {
                    for (final CommandNode dst : functionReturn.get(function))
                    {
                        edges.add(new Edge<TermTransitionPairsSet, LocationID>(locationMap.get(command), locationMap
                            .get(dst), TermTransitionPairsSet.EMPTY));
                    }
                }

            } else if (command instanceof ConditionalBranchCommandNode) {
                final BooleanExpressionNode cond = ((ConditionalBranchCommandNode) command).getCondition();
                final TRSTerm t = cond.toTerm();


                //                if (solver.isUNSAT(t)) {
                //                    t = ToolBox.buildFalse();
                //                } else if (solver.isUNSAT(ToolBox.buildNot(t))) {
                //                    t = ToolBox.buildTrue();
                //                }

                final CommandNode dst = labelMap.get(((BranchCommandNode) command).getBranchLabel());
                assert dst != null;

                //    for (final PolyConstraintsSystem c : disj.getConstraintsSystems()) {
                edges.add(new Edge<TermTransitionPairsSet, LocationID>(
                    locationMap.get(command),
                    locationMap.get(dst),
                    TermTransitionPairsSet.create(t, idRel)));
                //  }

                if (i < (commands.size() - 1)) {
                    //    for (final PolyConstraintsSystem c : disj.negate().getConstraintsSystems()) {
                    try {
                        edges.add(new Edge<TermTransitionPairsSet, LocationID>(
                            locationMap.get(command),
                            locationMap.get(commands.get(i + 1)),
                            TermTransitionPairsSet.create(
                                TermTools.negate(t),
                                idRel)));
                    } catch (final UnsupportedException e) {
                        throw new RuntimeException();
                    }
                    //  }
                }

            } else if (command instanceof BranchCommandNode) {
                final CommandNode dst = labelMap.get(((BranchCommandNode) command).getBranchLabel());
                assert dst != null;
                edges.add(new Edge<TermTransitionPairsSet, LocationID>(
                    locationMap.get(command),
                    locationMap.get(dst),
                    TermTransitionPairsSet.EMPTY));
            } else if (command instanceof CallCommandNode) {
                final CommandNode dst = labelMap.get(((CallCommandNode) command).getCallId());
                assert dst != null;
                edges.add(new Edge<TermTransitionPairsSet, LocationID>(
                    locationMap.get(command),
                    locationMap.get(dst),
                    TermTransitionPairsSet.EMPTY));

                final CallLocation l = (CallLocation) locationMap.get(command);

                final Location branchLocation = locationMap.get(dst);
                final Location returnLocation = locationMap.get(commands.get(i + 1));

                l.setLocations(returnLocation, branchLocation);

            } else if (i < (commands.size() - 1)
                && !(command instanceof StopCommandNode)
                && !(command instanceof AbortCommandNode))
            {
                edges
                .add(new Edge<TermTransitionPairsSet, LocationID>(locationMap.get(command), locationMap
                    .get(commands.get(i + 1)), TermTransitionPairsSet.EMPTY));
            }

        }


        return edges;
        }

    /**
     * @return A List of program locations with appropriate transitions for this program.
     */
    public ProgramGraph getProgramGraph() {

        final List<CommandNode> procCommands = GtpProgram.addNdtAssign(this.commands);

        final Map<CommandNode, Location> locationMap = GtpProgram.getLocationMap(procCommands);
        final Map<String, CommandNode> labelMap = GtpProgram.getLabelMap(procCommands);
        final Map<String, Set<CommandNode>> functionReturn = GtpProgram.getFunctionReturn(procCommands);

        final Set<Edge<TermTransitionPairsSet, LocationID>> edges =
            GtpProgram.getEdges(procCommands, locationMap, labelMap, functionReturn);

        final Location start = locationMap.get(procCommands.get(0));
        final ProgramGraph progGraph = new ProgramGraph(start, edges);
        return progGraph;

    }

}
