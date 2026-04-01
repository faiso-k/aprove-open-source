package aprove.input.Programs.jbc;

import java.util.*;

import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.Annotations.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * We get a string describing annotations for the arguments and static fields.
 *
 * This string is a sequence of parts separated by ";". Each part may be one of:
 * <ul>
 * <li>cx for some number x: argument x may be cyclic</li>
 * <li>nx for some number x: argument x may be non-tree</li>
 * <li>sx,y for some numbers x, y: arguments x and y may share (joins and =?=)</li>
 * <li>cS: every static field may be cyclic</li>
 * <li>nS: every static field may be non-tree</li>
 * <li>sSS: every static field may share with any other static field</li>
 * <li>sSA: every static field may share with any other reference</li>
 * </ul>
 * @author cotto
 */
public class StartStateAnnotator {
    /**
     * These arguments may be non-tree.
     */
    private final Collection<Integer> nonTree = new LinkedHashSet<>();

    /**
     * These arguments may be sharing.
     */
    private final Collection<Integer> cyclic = new LinkedHashSet<>();

    /**
     * These pairs of arguments may share.
     */
    private final CollectionMap<Integer, Integer> sharing = new CollectionMap<>();

    /**
     * Parse the string.
     * @param annotationsString the string to parse
     * @return an object giving information about how to annotate the start state and an object describing runtime
     * options (e.g. how to annotate new static fields)
     */
    public static Pair<StartStateAnnotator, RuntimeOptions> parse(final String annotationsString) {
        final StartStateAnnotator startStateAnnotator = new StartStateAnnotator();
        final StaticFieldInitInfo staticFieldInitInfo = new StaticFieldInitInfo();

        if (annotationsString == null) {
            return new Pair<>(startStateAnnotator, new RuntimeOptions(staticFieldInitInfo));
        }

        final String[] parts = annotationsString.split(";");
        for (final String part : parts) {
            switch (part) {
            case "cS":
                staticFieldInitInfo.setCyclic();
                continue;
            case "nS":
                staticFieldInitInfo.setNonTree();
                continue;
            case "sSS":
                staticFieldInitInfo.setSharingBetweenSFs();
                continue;
            case "sSA":
                staticFieldInitInfo.setSharingBetweenAny();
                continue;
            default:
                // we don't care
                break;
            }

            if (part.startsWith("c")) {
                final int arg = Integer.parseInt(part.substring(1));
                startStateAnnotator.cyclic.add(arg);
            } else if (part.startsWith("n")) {
                final int arg = Integer.parseInt(part.substring(1));
                startStateAnnotator.nonTree.add(arg);
            } else if (part.startsWith("s")) {
                final String[] args = part.substring(1).split(",");
                assert (args.length == 2);
                final int argOne = Integer.parseInt(args[0]);
                final int argTwo = Integer.parseInt(args[1]);
                startStateAnnotator.sharing.add(argOne, argTwo);
            }

        }

        return new Pair<>(startStateAnnotator, new RuntimeOptions(staticFieldInitInfo));
    }

    /**
     * Add annotations.
     * @param state the start state
     * @param argumentRefs the arguments of the start method
     */
    public void annotate(final State state, final List<AbstractVariableReference> argumentRefs) {
        final HeapAnnotations ha = state.getHeapAnnotations();
        final JoiningStructures joins = ha.getJoiningStructures();
        final EqualityGraph eqGraph = ha.getEqualityGraph();
        for (int i = 0; i < argumentRefs.size(); i++) {
            final AbstractVariableReference ref = argumentRefs.get(i);
            if (!ref.pointsToReferenceType() || ref.isNULLRef()) {
                continue;
            }
            if (this.cyclic.contains(i)) {
                joins.add(ref, ref);
                ha.setPossiblyNonTree(ref);
                ha.setPossiblyCyclic(ref, Collections.<HeapEdge>emptySet());
            } else if (this.nonTree.contains(i)) {
                joins.add(ref, ref);
                ha.setPossiblyNonTree(ref);
            }

            final Collection<Integer> sharesWith = this.sharing.getNotNull(i);
            for (int j = 0; j < argumentRefs.size(); j++) {
                if (sharesWith.contains(j)) {
                    final AbstractVariableReference other = argumentRefs.get(j);
                    if (!other.pointsToReferenceType() || other.isNULLRef()) {
                        continue;
                    }
                    joins.add(ref, other);
                    eqGraph.addPossibleEquality(state, ref, other);
                }
            }
        }
    }

}
