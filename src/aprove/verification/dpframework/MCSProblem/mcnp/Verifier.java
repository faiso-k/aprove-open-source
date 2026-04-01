package aprove.verification.dpframework.MCSProblem.mcnp;

import java.util.*;

import aprove.verification.dpframework.MCSProblem.mcnp.Constants.*;

/*
 * Verifies that given ranking function is indeed orients a set of MCGs
 */

public class Verifier {

    private String orderingType(final int fromInd,
        final ProgramPoint progPointFrom,
        final int toInd,
        final ProgramPoint progPointTo,
        final MCGraph mcg,
        final LevelMapping levelMapping,
        final String direction) {
        final String pointFromID = progPointFrom.getID();
        final String pointToID = progPointTo.getID();
        final Argument argFrom = progPointFrom.getArguments()[fromInd];
        final Argument argTo = progPointTo.getArguments()[toInd];

        //self edge
        if ((direction.equals(Constants.TOP_TO_TOP) || direction.equals(Constants.BOTTOM_TO_BOTTOM))
            && pointFromID.equals(pointToID) && fromInd == toInd) {
            return ">=";
        }

        final String relationType = mcg.getRelation(argFrom, argTo);

        if (relationType == null) {
            return null;
        } else if (relationType.equals(">")) {
            return ">";
        } else if (relationType.equals(">=")) {
            if (!(levelMapping instanceof TaggedLevelMapping)) {
                return ">=";
            } else if (levelMapping instanceof TaggedLevelMapping) {
                final String tagFrom = ((TaggedLevelMapping) levelMapping).getTag(progPointFrom.getID(), fromInd);
                final String tagTo = ((TaggedLevelMapping) levelMapping).getTag(progPointTo.getID(), toInd);
                final Integer tagFromInt = Integer.parseInt(tagFrom);
                final Integer tagToInt = Integer.parseInt(tagTo);
                if (tagFromInt.intValue() > tagToInt.intValue()) {
                    return ">";
                } else if (tagFromInt.intValue() >= tagToInt.intValue()) {
                    return ">=";
                } else {
                    return null;
                }
            }
        }
        return null;
    }

    // =========================== MC Graph Part Verification ==============================
    private void verifyMaxOrMin(final MCGraph mcg,
        final LevelMapping levelMapping,
        final HighLow fromPart,
        final HighLow toPart,
        final String direction,
        final boolean strictly,
        final String ordering) {
        boolean isMin = false; //for dms covering is backwards: x->y y covers x
        if (ordering.equals(Constants.MAX_ORDERING)) {
            isMin = false;
        } else if (ordering.equals(Constants.MIN_ORDERING)) {
            isMin = true;
        } else {
            throw new RuntimeException("Illegal ordering type: " + ordering + ".");
        }

        final String mcgID = mcg.getID();

        ProgramPoint progPointFrom = null;
        ProgramPoint progPointTo = null;

        String pointFromID = null;
        String pointToID = null;
        if (direction.equals(Constants.TOP_TO_BOTTOM)) {
            progPointFrom = mcg.getPointFrom();
            progPointTo = mcg.getPointTo();
        } else if (direction.equals(Constants.BOTTOM_TO_TOP)) {
            progPointFrom = mcg.getPointTo();
            progPointTo = mcg.getPointFrom();
        } else if (direction.equals(Constants.TOP_TO_TOP)) {
            progPointFrom = mcg.getPointFrom();
            progPointTo = mcg.getPointFrom();
        } else if (direction.equals(Constants.BOTTOM_TO_BOTTOM)) {
            progPointFrom = mcg.getPointTo();
            progPointTo = mcg.getPointTo();
        } else {
            assert (false);
        }

        pointFromID = progPointFrom.getID();
        pointToID = progPointTo.getID();

        Set<Integer> vertexes = null;
        switch (toPart) {
        case LOW:
            vertexes = levelMapping.getProgramPointFilteredArgumentsLo(pointToID);
            break;
        case HIGH:
            vertexes = levelMapping.getProgramPointFilteredArgumentsHi(pointToID);
            break;
        default:
            assert (false);
        }

        Set<Integer> coveringVertexes = null;
        switch (fromPart) {
        case LOW:
            coveringVertexes = levelMapping.getProgramPointFilteredArgumentsLo(pointFromID);
            break;
        case HIGH:
            coveringVertexes = levelMapping.getProgramPointFilteredArgumentsHi(pointFromID);
            break;
        default:
            assert (false);
        }

        if (isMin) {
            final Set<Integer> tmp = vertexes;
            vertexes = coveringVertexes;
            coveringVertexes = tmp;
        }

        for (final Integer v : vertexes) {
            boolean foundCover = false;
            for (final Iterator<Integer> it2 = coveringVertexes.iterator(); !foundCover && it2.hasNext();) {
                final Integer covering = it2.next();

                String relationType = null;
                if (!isMin) {
                    relationType = this.orderingType(covering, progPointFrom, v, progPointTo, mcg, levelMapping, direction);
                } else {
                    relationType = this.orderingType(v, progPointFrom, covering, progPointTo, mcg, levelMapping, direction);
                }
                foundCover =
                    relationType != null && (relationType.equals(">") || (!strictly && relationType.equals(">=")));

                if (Config.LOG_VERIFICATION && foundCover) {
                    Logger.writeDebug(covering + "->" + v);
                }
            }

            //one of the vertexes is not covered
            if (!foundCover) {
                final String msg =
                    "Graph: " + mcgID + " " + " vertex " + v + " is not covered (direction: " + direction + ").";
                Logger.writeReport(msg);
                throw new RuntimeException(msg);
            }
        }
    }

    //if strictly=true check if ordered strictly, else weakly
    private void verifyMSorDMS(final MCGraph mcg,
        final LevelMapping levelMapping,
        final HighLow fromPart,
        final HighLow toPart,
        final String direction,
        final boolean strictly,
        final String ordering) {
        boolean isDms = false; //for dms covering is backwards: x->y y covers x
        if (ordering.equals(Constants.MS_ORDERING)) {
            isDms = false;
        } else if (ordering.equals(Constants.DMS_ORDERING)) {
            isDms = true;
        } else {
            throw new RuntimeException("Illegal ordering type: " + ordering + ".");
        }

        final String mcgID = mcg.getID();

        ProgramPoint progPointFrom = null;
        ProgramPoint progPointTo = null;

        String pointFromID = null;
        String pointToID = null;
        if (direction.equals(Constants.TOP_TO_BOTTOM)) {
            progPointFrom = mcg.getPointFrom();
            progPointTo = mcg.getPointTo();
        } else if (direction.equals(Constants.BOTTOM_TO_TOP)) {
            progPointFrom = mcg.getPointTo();
            progPointTo = mcg.getPointFrom();
        } else {
            assert (false);
        }
        pointFromID = progPointFrom.getID();
        pointToID = progPointTo.getID();

        Set<Integer> vertexes = null;
        if (toPart.equals(Constants.HighLow.LOW)) {
            vertexes = levelMapping.getProgramPointFilteredArgumentsLo(pointToID);
        } else if (toPart.equals(Constants.HighLow.HIGH)) {
            vertexes = levelMapping.getProgramPointFilteredArgumentsHi(pointToID);
        }

        Set<Integer> coveringVertexes = null;
        if (fromPart.equals(Constants.HighLow.LOW)) {
            coveringVertexes = levelMapping.getProgramPointFilteredArgumentsLo(pointFromID);
        } else if (fromPart.equals(Constants.HighLow.HIGH)) {
            coveringVertexes = levelMapping.getProgramPointFilteredArgumentsHi(pointFromID);
        }

        if (isDms) {
            final Set<Integer> tmp = vertexes;
            vertexes = coveringVertexes;
            coveringVertexes = tmp;
        }

        final Set<Integer> usedVertexes = new HashSet<Integer>(); //vertexes which are covering. Used to handle {1,2,3} > {1,3}
        usedVertexes.addAll(coveringVertexes);

        final Set<Integer> strictlyCoveringVertexes = new HashSet<Integer>();

        for (final Integer v : vertexes) {

            // System.out.println(v+" "+mcgID+" "+direction); //D

            final Integer covering = levelMapping.getVertexCoverage(v, mcgID, direction);
            if (covering == null) {
                final String msg =
                    "Graph: " + mcgID + " " + " vertex " + v + " is not covered (direction: " + direction
                        + ") - no vertex.";
                Logger.writeReport(msg);
                throw new RuntimeException(msg);
            }
            String relationType = null;
            if (!isDms) {
                relationType = this.orderingType(covering, progPointFrom, v, progPointTo, mcg, levelMapping, direction);
            } else {
                relationType = this.orderingType(v, progPointFrom, covering, progPointTo, mcg, levelMapping, direction);
            }

            // System.out.println(covering+" "+progPointFrom.getID()+" "+v+" "+progPointTo.getID()+" "+relationType); //D

            if (relationType == null) {
                final String msg =
                    "Graph: " + mcgID + " " + " vertex " + v + " is not covered (direction: " + direction
                        + ") - no edge.";
                Logger.writeReport(msg);
                throw new RuntimeException(msg);
            } else if (relationType.equals(">=")) {
                if (strictlyCoveringVertexes.contains(covering)) {
                    final String msg =
                        "Graph: " + mcgID + " " + " vertex " + covering
                            + " is covering both strictly and weakly (direction: " + direction + ") - no vertex.";
                    Logger.writeReport(msg);
                    throw new RuntimeException(msg);
                }
                coveringVertexes.remove(covering); //strict edge - vertex may cover only one vertex
                if (usedVertexes.contains(covering)) {
                    usedVertexes.remove(covering);
                }
            } else if (relationType.equals(">")) {
                strictlyCoveringVertexes.add(covering);
                if (usedVertexes.contains(covering)) {
                    usedVertexes.remove(covering);
                }
            }
        }

        // ordering strictly if one edge i8s strict or covering set is bigger than the covered one.
        if (strictly && usedVertexes.isEmpty() && strictlyCoveringVertexes.isEmpty()) {
            final String msg = "The MC Graph: " + mcg.getID() + " is orcdred weakly instead of strictly ";
            Logger.writeReport(msg + "by:\n" + levelMapping);
            throw new RuntimeException("." + msg);
        }
    }

    private void verifyGraphPartMax(final MCGraph mcg,
        final LevelMapping levelMapping,
        final HighLow fromPart,
        final HighLow toPart,
        final String direction,
        final boolean strictly) {
        if (Config.LOG_VERIFICATION) {
            Logger.write("Varifying part max: " + "(direction=" + direction + "; from=" + fromPart + "; to=" + toPart
                + "; strictly=" + strictly + ")");
        }

        this.verifyMaxOrMin(mcg, levelMapping, fromPart, toPart, direction, strictly, Constants.MAX_ORDERING);
    }

    private void verifyGraphPartMin(final MCGraph mcg,
        final LevelMapping levelMapping,
        final HighLow fromPart,
        final HighLow toPart,
        final String direction,
        final boolean strictly) {
        if (Config.LOG_VERIFICATION) {
            Logger.write("Varifying part min: " + "(direction=" + direction + "; from=" + fromPart + "; to=" + toPart
                + "; strictly=" + strictly + ")");
        }

        this.verifyMaxOrMin(mcg, levelMapping, fromPart, toPart, direction, strictly, Constants.MIN_ORDERING);
    }

    private void verifyGraphPartMS(final MCGraph mcg,
        final LevelMapping levelMapping,
        final HighLow fromPart,
        final HighLow toPart,
        final String direction,
        final boolean strictly) {
        if (Config.LOG_VERIFICATION) {
            Logger.write("Varifying part ms: " + "(direction=" + direction + "; from=" + fromPart + "; to=" + toPart
                + "; strictly=" + strictly + ")");
        }

        this.verifyMSorDMS(mcg, levelMapping, fromPart, toPart, direction, strictly, Constants.MS_ORDERING);
    }

    private void verifyGraphPartDMS(final MCGraph mcg,
        final LevelMapping levelMapping,
        final HighLow fromPart,
        final HighLow toPart,
        final String direction,
        final boolean strictly) {
        if (Config.LOG_VERIFICATION) {
            Logger.write("Varifying part dms: " + "(direction=" + direction + "; from=" + fromPart + "; to=" + toPart
                + "; strictly=" + strictly + ")");
        }

        this.verifyMSorDMS(mcg, levelMapping, fromPart, toPart, direction, strictly, Constants.DMS_ORDERING);
    }

    private void verifyGraphPartMaxGtMin(final MCGraph mcg,
        final LevelMapping levelMapping,
        final HighLow fromPart,
        final HighLow toPart,
        final String direction,
        final boolean strictly) {
        if (Config.LOG_VERIFICATION) {
            Logger.write("Varifying part max>=min: " + "(direction=" + direction + "; from=" + fromPart + "; to="
                + toPart + "; strictly=" + strictly + ")");
        }

        final String mcgID = mcg.getID();

        ProgramPoint progPointFrom = null;
        ProgramPoint progPointTo = null;

        String pointFromID = null;
        String pointToID = null;
        if (direction.equals(Constants.TOP_TO_BOTTOM)) {
            progPointFrom = mcg.getPointFrom();
            progPointTo = mcg.getPointTo();
        } else if (direction.equals(Constants.BOTTOM_TO_TOP)) {
            progPointFrom = mcg.getPointTo();
            progPointTo = mcg.getPointFrom();
        } else if (direction.equals(Constants.TOP_TO_TOP)) {
            progPointFrom = mcg.getPointFrom();
            progPointTo = mcg.getPointFrom();
        } else if (direction.equals(Constants.BOTTOM_TO_BOTTOM)) {
            progPointFrom = mcg.getPointTo();
            progPointTo = mcg.getPointTo();
        } else {
            assert (false);
        }

        pointFromID = progPointFrom.getID();
        pointToID = progPointTo.getID();

        Set<Integer> vertexes = null;
        if (toPart.equals(Constants.HighLow.LOW)) {
            vertexes = levelMapping.getProgramPointFilteredArgumentsLo(pointToID);
        } else if (toPart.equals(Constants.HighLow.HIGH)) {
            vertexes = levelMapping.getProgramPointFilteredArgumentsHi(pointToID);
        }

        Set<Integer> coveringVertexes = null;
        if (fromPart.equals(Constants.HighLow.LOW)) {
            coveringVertexes = levelMapping.getProgramPointFilteredArgumentsLo(pointFromID);
        } else if (fromPart.equals(Constants.HighLow.HIGH)) {
            coveringVertexes = levelMapping.getProgramPointFilteredArgumentsHi(pointFromID);
        } else {
            assert (false);
        }

        boolean foundCover = false;
        for (final Iterator<Integer> it = vertexes.iterator(); !foundCover && it.hasNext();) {
            final Integer v = it.next();
            for (final Iterator<Integer> it2 = coveringVertexes.iterator(); !foundCover && it2.hasNext();) {
                final Integer covering = it2.next();
                final String relationType =
                    this.orderingType(covering, progPointFrom, v, progPointTo, mcg, levelMapping, direction);

                foundCover =
                    relationType != null && (relationType.equals(">") || (!strictly && relationType.equals(">=")));
                if (Config.LOG_VERIFICATION && foundCover) {
                    Logger.writeDebug(covering + "->" + v);
                }
            }
        }

        if (!foundCover) {
            final String msg = "Graph: " + mcgID + " " + " no edge (direction: " + direction + ").";
            Logger.writeReport(msg);
            throw new RuntimeException(msg);
        }
    }

    private void verifyGraphPartMinGtMax(final MCGraph mcg,
        final LevelMapping levelMapping,
        final HighLow fromPart,
        final HighLow toPart,
        final String direction,
        final boolean strictly) {
        if (Config.LOG_VERIFICATION) {
            Logger.write("Varifying part min>=max: " + "(direction=" + direction + "; from=" + fromPart + "; to="
                + toPart + "; strictly=" + strictly + ")");
        }

        final String mcgID = mcg.getID();

        ProgramPoint progPointFrom = null;
        ProgramPoint progPointTo = null;

        String pointFromID = null;
        String pointToID = null;
        if (direction.equals(Constants.TOP_TO_BOTTOM)) {
            progPointFrom = mcg.getPointFrom();
            progPointTo = mcg.getPointTo();
        } else if (direction.equals(Constants.BOTTOM_TO_TOP)) {
            progPointFrom = mcg.getPointTo();
            progPointTo = mcg.getPointFrom();
        } else if (direction.equals(Constants.TOP_TO_TOP)) {
            progPointFrom = mcg.getPointFrom();
            progPointTo = mcg.getPointFrom();
        } else if (direction.equals(Constants.BOTTOM_TO_BOTTOM)) {
            progPointFrom = mcg.getPointTo();
            progPointTo = mcg.getPointTo();
        } else {
            assert (false);
        }

        pointFromID = progPointFrom.getID();
        pointToID = progPointTo.getID();

        Set<Integer> vertexes = null;
        if (toPart.equals(Constants.HighLow.LOW)) {
            vertexes = levelMapping.getProgramPointFilteredArgumentsLo(pointToID);
        } else if (toPart.equals(Constants.HighLow.HIGH)) {
            vertexes = levelMapping.getProgramPointFilteredArgumentsHi(pointToID);
        }

        Set<Integer> coveringVertexes = null;
        if (fromPart.equals(Constants.HighLow.LOW)) {
            coveringVertexes = levelMapping.getProgramPointFilteredArgumentsLo(pointFromID);
        } else if (fromPart.equals(Constants.HighLow.HIGH)) {
            coveringVertexes = levelMapping.getProgramPointFilteredArgumentsHi(pointFromID);
        } else {
            assert (false);
        }

        for (final Integer v : vertexes) {
            boolean foundCover = false;
            for (final Integer covering : coveringVertexes) {
                final String relationType =
                    this.orderingType(covering, progPointFrom, v, progPointTo, mcg, levelMapping, direction);

                foundCover =
                    relationType != null && (relationType.equals(">") || (!strictly && relationType.equals(">=")));
                if (Config.LOG_VERIFICATION && foundCover) {
                    Logger.writeDebug(covering + "->" + v);
                }

                if (!foundCover) {
                    final String msg =
                        "Graph: " + mcgID + " " + " no edge " + covering + "->" + v + " (direction: " + direction
                            + ").";
                    Logger.writeReport(msg);
                    throw new RuntimeException(msg);
                }
            }
        }
    }

    private void verifyGraphPart(final MCGraph mcg,
        final LevelMapping levelMapping,
        final HighLow fromPart,
        final HighLow toPart,
        final String direction,
        final boolean strictly,
        final String ordering) {
        if (ordering.equals(Constants.MAX_ORDERING)) {
            this.verifyGraphPartMax(mcg, levelMapping, fromPart, toPart, direction, strictly);
        } else if (ordering.equals(Constants.MIN_ORDERING)) {
            this.verifyGraphPartMin(mcg, levelMapping, fromPart, toPart, direction, strictly);
        } else if (ordering.equals(Constants.MS_ORDERING)) {
            this.verifyGraphPartMS(mcg, levelMapping, fromPart, toPart, direction, strictly);
        } else if (ordering.equals(Constants.DMS_ORDERING)) {
            this.verifyGraphPartDMS(mcg, levelMapping, fromPart, toPart, direction, strictly);
        } else if (ordering.equals(Constants.MAX_GT_MIN_ORDERING)) {
            this.verifyGraphPartMaxGtMin(mcg, levelMapping, fromPart, toPart, direction, strictly);
        } else if (ordering.equals(Constants.MIN_GT_MAX_ORDERING)) {
            this.verifyGraphPartMinGtMax(mcg, levelMapping, fromPart, toPart, direction, strictly);
        } else {
            throw new RuntimeException("Illegal ordering: " + ordering + ".");
        }
    }

    // =========================== MC Graph Part Verification (end) ==============================

    private void verifyOrdering_cutsetMethod1(final MCGraph mcg,
        final LevelMapping levelMapping,
        final String ordering,
        final String orderingLo,
        final String orderingHi,
        final String orderingTop,
        final boolean strictIncWeakDec) {
        if (Config.LOG_VERIFICATION) {
            if (strictIncWeakDec) {
                Logger.write("Verification StrictInc: " + ordering + " " + orderingLo + " " + orderingHi + " "
                    + orderingTop);
            } else {
                Logger.write("Verification StrictDec: " + ordering + " " + orderingLo + " " + orderingHi + " "
                    + orderingTop);
            }
        }

        final String progPointFrom = mcg.getPointFrom().getID();
        final String progPointTo = mcg.getPointTo().getID();

        final boolean isBound =
            levelMapping.getProgPointBoundNumber(progPointFrom) < levelMapping.getProgPointBoundNumber(progPointTo);

        final boolean isRemovable = levelMapping.getRemovableGraphs().contains(mcg.getID());
        final boolean removableSelfBound =
            isRemovable
                && levelMapping.getProgPointBoundNumber(progPointFrom).equals(
                    levelMapping.getProgPointBoundNumber(progPointTo));

        if (strictIncWeakDec) {
            if (isRemovable) {
                this.verifyGraphPart(mcg, levelMapping, Constants.HighLow.LOW, Constants.HighLow.LOW,
                    Constants.BOTTOM_TO_TOP, true,
                    orderingLo); //strict
            } else {
                this.verifyGraphPart(mcg, levelMapping, Constants.HighLow.LOW, Constants.HighLow.LOW,
                    Constants.BOTTOM_TO_TOP, false,
                    orderingLo);
            }
            this.verifyGraphPart(mcg, levelMapping, Constants.HighLow.HIGH, Constants.HighLow.HIGH, Constants.TOP_TO_BOTTOM,
                false, orderingHi);
        } else {
            this.verifyGraphPart(mcg, levelMapping, Constants.HighLow.LOW, Constants.HighLow.LOW,
                Constants.BOTTOM_TO_TOP, false, orderingLo);
            if (isRemovable) {
                this.verifyGraphPart(mcg, levelMapping, Constants.HighLow.HIGH, Constants.HighLow.HIGH,
                    Constants.TOP_TO_BOTTOM, true,
                    orderingHi); //strict
            } else {
                this.verifyGraphPart(mcg, levelMapping, Constants.HighLow.HIGH, Constants.HighLow.HIGH,
                    Constants.TOP_TO_BOTTOM, false,
                    orderingHi);
            }
        }

        if (isBound || removableSelfBound) {
            this.verifyGraphPart(mcg, levelMapping, Constants.HighLow.HIGH, Constants.HighLow.LOW,
                Constants.TOP_TO_TOP, false, orderingTop);
        }
    }

    private void verifyOrdering_cutsetMethod2(final MCGraph mcg,
        final LevelMapping levelMapping,
        final String ordering,
        final String orderingLo,
        final String orderingHi,
        final String orderingTop,
        final boolean strictIncWeakDec) {
        if (Config.LOG_VERIFICATION) {
            if (strictIncWeakDec) {
                Logger.write("Verification StrictInc: " + ordering + " " + orderingLo + " " + orderingHi + " "
                    + orderingTop);
            } else {
                Logger.write("Verification StrictDec: " + ordering + " " + orderingLo + " " + orderingHi + " "
                    + orderingTop);
            }
        }

        final String progPointFrom = mcg.getPointFrom().getID();
        final String progPointTo = mcg.getPointTo().getID();

        final boolean isStrict =
            levelMapping.getProgPointStrictNumber(progPointFrom) < levelMapping.getProgPointStrictNumber(progPointTo);
        final boolean isBound =
            levelMapping.getProgPointBoundNumber(progPointFrom) < levelMapping.getProgPointBoundNumber(progPointTo);

        final boolean isRemovable = levelMapping.getRemovableGraphs().contains(mcg.getID());
        final boolean removableSelfBound =
            isRemovable
                && levelMapping.getProgPointBoundNumber(progPointFrom).equals(
                    levelMapping.getProgPointBoundNumber(progPointTo));
        final boolean removableSelfStrict =
            isRemovable
                && levelMapping.getProgPointStrictNumber(progPointFrom).equals(
                    levelMapping.getProgPointStrictNumber(progPointTo));

        if (strictIncWeakDec) {
            if (isStrict || removableSelfStrict) {
                this.verifyGraphPart(mcg, levelMapping, Constants.HighLow.LOW, Constants.HighLow.LOW,
                    Constants.BOTTOM_TO_TOP, true,
                    orderingLo); //strict
            } else {
                this.verifyGraphPart(mcg, levelMapping, Constants.HighLow.LOW, Constants.HighLow.LOW,
                    Constants.BOTTOM_TO_TOP, false,
                    orderingLo);
            }
            this.verifyGraphPart(mcg, levelMapping, Constants.HighLow.HIGH, Constants.HighLow.HIGH, Constants.TOP_TO_BOTTOM,
                false, orderingHi);
        } else {
            this.verifyGraphPart(mcg, levelMapping, Constants.HighLow.LOW, Constants.HighLow.LOW,
                Constants.BOTTOM_TO_TOP, false, orderingLo);
            if (isStrict || removableSelfStrict) {
                this.verifyGraphPart(mcg, levelMapping, Constants.HighLow.HIGH, Constants.HighLow.HIGH,
                    Constants.TOP_TO_BOTTOM, true,
                    orderingHi); //strict
            } else {
                this.verifyGraphPart(mcg, levelMapping, Constants.HighLow.HIGH, Constants.HighLow.HIGH,
                    Constants.TOP_TO_BOTTOM, false,
                    orderingHi);
            }

        }

        if (isBound || removableSelfBound) {
            this.verifyGraphPart(mcg, levelMapping, Constants.HighLow.HIGH, Constants.HighLow.LOW,
                Constants.TOP_TO_TOP, false, orderingTop);
        }
    }

    private void verifyOrdering(final MCGraph mcg,
        final LevelMapping levelMapping,
        final String ordering,
        final String orderingLo,
        final String orderingHi,
        final String orderingTop,
        final boolean strictIncWeakDec) {
        if (Config.CUTSET_METHOD_2) {
            this.verifyOrdering_cutsetMethod2(mcg, levelMapping, ordering, orderingLo, orderingHi, orderingTop,
                strictIncWeakDec);
        } else {
            this.verifyOrdering_cutsetMethod1(mcg, levelMapping, ordering, orderingLo, orderingHi, orderingTop,
                strictIncWeakDec);
        }
    }

    private void verifyOrderingStrictIncWeakDec(final MCGraph mcg,
        final LevelMapping levelMapping,
        final String ordering,
        final String orderingLo,
        final String orderingHi,
        final String orderingTop) {
        this.verifyOrdering(mcg, levelMapping, ordering, orderingLo, orderingHi, orderingTop, true);
    }

    private void verifyOrderingStrictDecWeakInc(final MCGraph mcg,
        final LevelMapping levelMapping,
        final String ordering,
        final String orderingLo,
        final String orderingHi,
        final String orderingTop) {
        this.verifyOrdering(mcg, levelMapping, ordering, orderingLo, orderingHi, orderingTop, false);
    }

    // ms/max , ms/max | max
    private void maxMaxMaxOrderingStrictIncWeakDec(final MCGraph mcg, final LevelMapping levelMapping) {
        this.verifyOrderingStrictIncWeakDec(mcg, levelMapping, Constants.GRAPH_SW_MAX_MAX_MAX_ORDERING,
            Constants.MAX_ORDERING, Constants.MAX_ORDERING, Constants.MAX_ORDERING);
    }

    private void maxMaxMaxOrderingWeakIncStrictDec(final MCGraph mcg, final LevelMapping levelMapping) {
        this.verifyOrderingStrictDecWeakInc(mcg, levelMapping, Constants.GRAPH_WS_MAX_MAX_MAX_ORDERING,
            Constants.MAX_ORDERING, Constants.MAX_ORDERING, Constants.MAX_ORDERING);
    }

    private void msMsMaxOrderingStrictIncWeakDec(final MCGraph mcg, final LevelMapping levelMapping) {
        this.verifyOrderingStrictIncWeakDec(mcg, levelMapping, Constants.GRAPH_SW_MS_MS_MAX_ORDERING, Constants.MS_ORDERING,
            Constants.MS_ORDERING, Constants.MAX_ORDERING);
    }

    private void msMsMaxOrderingWeakIncStrictDec(final MCGraph mcg, final LevelMapping levelMapping) {
        this.verifyOrderingStrictDecWeakInc(mcg, levelMapping, Constants.GRAPH_WS_MS_MS_MAX_ORDERING, Constants.MS_ORDERING,
            Constants.MS_ORDERING, Constants.MAX_ORDERING);
    }

    private void msMaxMaxOrderingStrictIncWeakDec(final MCGraph mcg, final LevelMapping levelMapping) {
        this.verifyOrderingStrictIncWeakDec(mcg, levelMapping, Constants.GRAPH_SW_MS_MAX_MAX_ORDERING,
            Constants.MS_ORDERING, Constants.MAX_ORDERING, Constants.MAX_ORDERING);
    }

    private void msMaxMaxOrderingWeakIncStrictDec(final MCGraph mcg, final LevelMapping levelMapping) {
        this.verifyOrderingStrictDecWeakInc(mcg, levelMapping, Constants.GRAPH_WS_MS_MAX_MAX_ORDERING,
            Constants.MS_ORDERING, Constants.MAX_ORDERING, Constants.MAX_ORDERING);
    }

    private void maxMsMaxOrderingStrictIncWeakDec(final MCGraph mcg, final LevelMapping levelMapping) {
        this.verifyOrderingStrictIncWeakDec(mcg, levelMapping, Constants.GRAPH_SW_MAX_MS_MAX_ORDERING,
            Constants.MAX_ORDERING, Constants.MS_ORDERING, Constants.MAX_ORDERING);
    }

    private void maxMsMaxOrderingWeakIncStrictDec(final MCGraph mcg, final LevelMapping levelMapping) {
        this.verifyOrderingStrictDecWeakInc(mcg, levelMapping, Constants.GRAPH_WS_MAX_MS_MAX_ORDERING,
            Constants.MAX_ORDERING, Constants.MS_ORDERING, Constants.MAX_ORDERING);
    }

    // dms , max | max
    private void dmsMaxMaxOrderingStrictIncWeakDec(final MCGraph mcg, final LevelMapping levelMapping) {
        this.verifyOrderingStrictIncWeakDec(mcg, levelMapping, Constants.GRAPH_SW_DMS_MAX_MAX_ORDERING,
            Constants.DMS_ORDERING, Constants.MAX_ORDERING, Constants.MAX_ORDERING);
    }

    private void dmsMaxMaxOrderingWeakIncStrictDec(final MCGraph mcg, final LevelMapping levelMapping) {
        this.verifyOrderingStrictDecWeakInc(mcg, levelMapping, Constants.GRAPH_WS_DMS_MAX_MAX_ORDERING,
            Constants.DMS_ORDERING, Constants.MAX_ORDERING, Constants.MAX_ORDERING);
    }

    // min  , min | min
    private void minMinMinOrderingStrictIncWeakDec(final MCGraph mcg, final LevelMapping levelMapping) {
        this.verifyOrderingStrictIncWeakDec(mcg, levelMapping, Constants.GRAPH_SW_MIN_MIN_MIN_ORDERING,
            Constants.MIN_ORDERING, Constants.MIN_ORDERING, Constants.MIN_ORDERING);
    }

    private void minMinMinOrderingWeakIncStrictDec(final MCGraph mcg, final LevelMapping levelMapping) {
        this.verifyOrderingStrictDecWeakInc(mcg, levelMapping, Constants.GRAPH_WS_MIN_MIN_MIN_ORDERING,
            Constants.MIN_ORDERING, Constants.MIN_ORDERING, Constants.MIN_ORDERING);
    }

    //min , max/ms | max>min
    private void minMaxMaxminOrderingStrictIncWeakDec(final MCGraph mcg, final LevelMapping levelMapping) {
        this.verifyOrderingStrictIncWeakDec(mcg, levelMapping, Constants.GRAPH_SW_MIN_MAX_MAXMIN_ORDERING,
            Constants.MIN_ORDERING, Constants.MAX_ORDERING, Constants.MAX_GT_MIN_ORDERING);
    }

    private void minMaxMaxminOrderingWeakIncStrictDec(final MCGraph mcg, final LevelMapping levelMapping) {
        this.verifyOrderingStrictDecWeakInc(mcg, levelMapping, Constants.GRAPH_WS_MIN_MAX_MAXMIN_ORDERING,
            Constants.MIN_ORDERING, Constants.MAX_ORDERING, Constants.MAX_GT_MIN_ORDERING);
    }

    private void minMsMaxminOrderingStrictIncWeakDec(final MCGraph mcg, final LevelMapping levelMapping) {
        this.verifyOrderingStrictIncWeakDec(mcg, levelMapping, Constants.GRAPH_SW_MIN_MS_MAXMIN_ORDERING,
            Constants.MIN_ORDERING, Constants.MS_ORDERING, Constants.MAX_GT_MIN_ORDERING);
    }

    private void minMsMaxminOrderingWeakIncStrictDec(final MCGraph mcg, final LevelMapping levelMapping) {
        this.verifyOrderingStrictDecWeakInc(mcg, levelMapping, Constants.GRAPH_WS_MIN_MS_MAXMIN_ORDERING,
            Constants.MIN_ORDERING, Constants.MS_ORDERING, Constants.MAX_GT_MIN_ORDERING);
    }

    //max/ms/dms , min | min>=max
    private void maxMinMinmaxOrderingStrictIncWeakDec(final MCGraph mcg, final LevelMapping levelMapping) {
        this.verifyOrderingStrictIncWeakDec(mcg, levelMapping, Constants.GRAPH_SW_MAX_MIN_MINMAX_ORDERING,
            Constants.MAX_ORDERING, Constants.MIN_ORDERING, Constants.MIN_GT_MAX_ORDERING);
    }

    private void maxMinMinmaxOrderingWeakIncStrictDec(final MCGraph mcg, final LevelMapping levelMapping) {
        this.verifyOrderingStrictDecWeakInc(mcg, levelMapping, Constants.GRAPH_WS_MAX_MIN_MINMAX_ORDERING,
            Constants.MAX_ORDERING, Constants.MIN_ORDERING, Constants.MIN_GT_MAX_ORDERING);
    }

    private void msMinMinmaxOrderingStrictIncWeakDec(final MCGraph mcg, final LevelMapping levelMapping) {
        this.verifyOrderingStrictIncWeakDec(mcg, levelMapping, Constants.GRAPH_SW_MS_MIN_MINMAX_ORDERING,
            Constants.MS_ORDERING, Constants.MIN_ORDERING, Constants.MIN_GT_MAX_ORDERING);
    }

    private void msMinMinmaxOrderingWeakIncStrictDec(final MCGraph mcg, final LevelMapping levelMapping) {
        this.verifyOrderingStrictDecWeakInc(mcg, levelMapping, Constants.GRAPH_WS_MS_MIN_MINMAX_ORDERING,
            Constants.MS_ORDERING, Constants.MIN_ORDERING, Constants.MIN_GT_MAX_ORDERING);
    }

    private void dmsMinMinmaxOrderingStrictIncWeakDec(final MCGraph mcg, final LevelMapping levelMapping) {
        this.verifyOrderingStrictIncWeakDec(mcg, levelMapping, Constants.GRAPH_SW_DMS_MIN_MINMAX_ORDERING,
            Constants.DMS_ORDERING, Constants.MIN_ORDERING, Constants.MIN_GT_MAX_ORDERING);
    }

    private void dmsMinMinmaxOrderingWeakIncStrictDec(final MCGraph mcg, final LevelMapping levelMapping) {
        this.verifyOrderingStrictDecWeakInc(mcg, levelMapping, Constants.GRAPH_WS_DMS_MIN_MINMAX_ORDERING,
            Constants.DMS_ORDERING, Constants.MIN_ORDERING, Constants.MIN_GT_MAX_ORDERING);
    }

    //max , ms/dms | min>=max
    private void maxMsMinmaxOrderingStrictIncWeakDec(final MCGraph mcg, final LevelMapping levelMapping) {
        this.verifyOrderingStrictIncWeakDec(mcg, levelMapping, Constants.GRAPH_SW_MAX_MS_MINMAX_ORDERING,
            Constants.MAX_ORDERING, Constants.MS_ORDERING, Constants.MIN_GT_MAX_ORDERING);
    }

    private void maxMsMinmaxOrderingWeakIncStrictDec(final MCGraph mcg, final LevelMapping levelMapping) {
        this.verifyOrderingStrictDecWeakInc(mcg, levelMapping, Constants.GRAPH_WS_MAX_MS_MINMAX_ORDERING,
            Constants.MAX_ORDERING, Constants.MS_ORDERING, Constants.MIN_GT_MAX_ORDERING);
    }

    private void maxDmsMinmaxOrderingStrictIncWeakDec(final MCGraph mcg, final LevelMapping levelMapping) {
        this.verifyOrderingStrictIncWeakDec(mcg, levelMapping, Constants.GRAPH_SW_MAX_DMS_MINMAX_ORDERING,
            Constants.MAX_ORDERING, Constants.DMS_ORDERING, Constants.MIN_GT_MAX_ORDERING);
    }

    private void maxDmsMinmaxOrderingWeakIncStrictDec(final MCGraph mcg, final LevelMapping levelMapping) {
        this.verifyOrderingStrictDecWeakInc(mcg, levelMapping, Constants.GRAPH_WS_MAX_DMS_MINMAX_ORDERING,
            Constants.MAX_ORDERING, Constants.DMS_ORDERING, Constants.MIN_GT_MAX_ORDERING);
    }

    //min , ms/dms | min
    private void minMsMinOrderingStrictIncWeakDec(final MCGraph mcg, final LevelMapping levelMapping) {
        this.verifyOrderingStrictIncWeakDec(mcg, levelMapping, Constants.GRAPH_SW_MIN_MS_MIN_ORDERING,
            Constants.MIN_ORDERING, Constants.MS_ORDERING, Constants.MIN_ORDERING);
    }

    private void minMsMinOrderingWeakIncStrictDec(final MCGraph mcg, final LevelMapping levelMapping) {
        this.verifyOrderingStrictDecWeakInc(mcg, levelMapping, Constants.GRAPH_WS_MIN_MS_MIN_ORDERING,
            Constants.MIN_ORDERING, Constants.MS_ORDERING, Constants.MIN_ORDERING);
    }

    private void minDmsMinOrderingStrictIncWeakDec(final MCGraph mcg, final LevelMapping levelMapping) {
        this.verifyOrderingStrictIncWeakDec(mcg, levelMapping, Constants.GRAPH_SW_MIN_DMS_MIN_ORDERING,
            Constants.MIN_ORDERING, Constants.DMS_ORDERING, Constants.MIN_ORDERING);
    }

    private void minDmsMinOrderingWeakIncStrictDec(final MCGraph mcg, final LevelMapping levelMapping) {
        this.verifyOrderingStrictDecWeakInc(mcg, levelMapping, Constants.GRAPH_WS_MIN_DMS_MIN_ORDERING,
            Constants.MIN_ORDERING, Constants.DMS_ORDERING, Constants.MIN_ORDERING);
    }

    private void verifyGraph(final MCGraph mcg, final LevelMapping levelMapping) {
        final String ordering = levelMapping.getType();

        //max/ms , max/ms
        if (ordering.equals(Constants.GRAPH_SW_MAX_MAX_MAX_ORDERING)) {
            this.maxMaxMaxOrderingStrictIncWeakDec(mcg, levelMapping);
        } else if (ordering.equals(Constants.GRAPH_WS_MAX_MAX_MAX_ORDERING)) {
            this.maxMaxMaxOrderingWeakIncStrictDec(mcg, levelMapping);
        } else if (ordering.equals(Constants.GRAPH_SW_MS_MS_MAX_ORDERING)) {
            this.msMsMaxOrderingStrictIncWeakDec(mcg, levelMapping);
        } else if (ordering.equals(Constants.GRAPH_WS_MS_MS_MAX_ORDERING)) {
            this.msMsMaxOrderingWeakIncStrictDec(mcg, levelMapping);
        } else if (ordering.equals(Constants.GRAPH_SW_MS_MAX_MAX_ORDERING)) {
            this.msMaxMaxOrderingStrictIncWeakDec(mcg, levelMapping);
        } else if (ordering.equals(Constants.GRAPH_WS_MS_MAX_MAX_ORDERING)) {
            this.msMaxMaxOrderingWeakIncStrictDec(mcg, levelMapping);
        } else if (ordering.equals(Constants.GRAPH_SW_MAX_MS_MAX_ORDERING)) {
            this.maxMsMaxOrderingStrictIncWeakDec(mcg, levelMapping);
        } else if (ordering.equals(Constants.GRAPH_WS_MAX_MS_MAX_ORDERING)) {
            this.maxMsMaxOrderingWeakIncStrictDec(mcg, levelMapping);
        } else if (ordering.equals(Constants.GRAPH_SW_DMS_MAX_MAX_ORDERING)) {
            this.dmsMaxMaxOrderingStrictIncWeakDec(mcg, levelMapping);
        } else if (ordering.equals(Constants.GRAPH_WS_DMS_MAX_MAX_ORDERING)) {
            this.dmsMaxMaxOrderingWeakIncStrictDec(mcg, levelMapping);
        } else if (ordering.equals(Constants.GRAPH_SW_MIN_MIN_MIN_ORDERING)) {
            this.minMinMinOrderingStrictIncWeakDec(mcg, levelMapping);
        } else if (ordering.equals(Constants.GRAPH_WS_MIN_MIN_MIN_ORDERING)) {
            this.minMinMinOrderingWeakIncStrictDec(mcg, levelMapping);
        } else if (ordering.equals(Constants.GRAPH_SW_MIN_MAX_MAXMIN_ORDERING)) {
            this.minMaxMaxminOrderingStrictIncWeakDec(mcg, levelMapping);
        } else if (ordering.equals(Constants.GRAPH_WS_MIN_MAX_MAXMIN_ORDERING)) {
            this.minMaxMaxminOrderingWeakIncStrictDec(mcg, levelMapping);
        } else if (ordering.equals(Constants.GRAPH_SW_MIN_MS_MAXMIN_ORDERING)) {
            this.minMsMaxminOrderingStrictIncWeakDec(mcg, levelMapping);
        } else if (ordering.equals(Constants.GRAPH_WS_MIN_MS_MAXMIN_ORDERING)) {
            this.minMsMaxminOrderingWeakIncStrictDec(mcg, levelMapping);
        } else if (ordering.equals(Constants.GRAPH_SW_MAX_MIN_MINMAX_ORDERING)) {
            this.maxMinMinmaxOrderingStrictIncWeakDec(mcg, levelMapping);
        } else if (ordering.equals(Constants.GRAPH_WS_MAX_MIN_MINMAX_ORDERING)) {
            this.maxMinMinmaxOrderingWeakIncStrictDec(mcg, levelMapping);
        } else if (ordering.equals(Constants.GRAPH_SW_MS_MIN_MINMAX_ORDERING)) {
            this.msMinMinmaxOrderingStrictIncWeakDec(mcg, levelMapping);
        } else if (ordering.equals(Constants.GRAPH_WS_MS_MIN_MINMAX_ORDERING)) {
            this.msMinMinmaxOrderingWeakIncStrictDec(mcg, levelMapping);
        } else if (ordering.equals(Constants.GRAPH_SW_DMS_MIN_MINMAX_ORDERING)) {
            this.dmsMinMinmaxOrderingStrictIncWeakDec(mcg, levelMapping);
        } else if (ordering.equals(Constants.GRAPH_WS_DMS_MIN_MINMAX_ORDERING)) {
            this.dmsMinMinmaxOrderingWeakIncStrictDec(mcg, levelMapping);
        } else if (ordering.equals(Constants.GRAPH_SW_MAX_MS_MINMAX_ORDERING)) {
            this.maxMsMinmaxOrderingStrictIncWeakDec(mcg, levelMapping);
        } else if (ordering.equals(Constants.GRAPH_WS_MAX_MS_MINMAX_ORDERING)) {
            this.maxMsMinmaxOrderingWeakIncStrictDec(mcg, levelMapping);
        } else if (ordering.equals(Constants.GRAPH_SW_MAX_DMS_MINMAX_ORDERING)) {
            this.maxDmsMinmaxOrderingStrictIncWeakDec(mcg, levelMapping);
        } else if (ordering.equals(Constants.GRAPH_WS_MAX_DMS_MINMAX_ORDERING)) {
            this.maxDmsMinmaxOrderingWeakIncStrictDec(mcg, levelMapping);
        } else if (ordering.equals(Constants.GRAPH_SW_MIN_MS_MIN_ORDERING)) {
            this.minMsMinOrderingStrictIncWeakDec(mcg, levelMapping);
        } else if (ordering.equals(Constants.GRAPH_WS_MIN_MS_MIN_ORDERING)) {
            this.minMsMinOrderingWeakIncStrictDec(mcg, levelMapping);
        } else if (ordering.equals(Constants.GRAPH_SW_MIN_DMS_MIN_ORDERING)) {
            this.minDmsMinOrderingStrictIncWeakDec(mcg, levelMapping);
        } else if (ordering.equals(Constants.GRAPH_WS_MIN_DMS_MIN_ORDERING)) {
            this.minDmsMinOrderingWeakIncStrictDec(mcg, levelMapping);
        } else {
            throw new RuntimeException("Illegal ordering type: " + ordering + ".");
        }
    }

    public void verify(final List<MCGraph> mcGraphs, final List<MCGraphMapping> rankingFunction) {
        if (Config.LOG_VERIFICATION) {
            Logger.writeReport("================= Verifying Ranking Function =====================");
            Logger.writeReport(rankingFunction.toString());
        }
        for (final MCGraphMapping mapping : rankingFunction) {
            if (mapping instanceof LevelMapping) {
                final LevelMapping levelMapping = (LevelMapping) mapping;
                for (final MCGraph mcg : mcGraphs) {
                    if (levelMapping.getWeakOrderedGraphs().contains(mcg.getID())
                        || levelMapping.getStrictOrderedGraphs().contains(mcg.getID())) {
                        this.verifyGraph(mcg, levelMapping);
                    }
                }
            }
        }
    }
}
