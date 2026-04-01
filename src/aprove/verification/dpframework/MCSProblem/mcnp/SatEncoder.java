package aprove.verification.dpframework.MCSProblem.mcnp;

import java.util.*;

import aprove.verification.dpframework.MCSProblem.mcnp.Constants.*;
import aprove.verification.dpframework.MCSProblem.sat_tools.*;

/*
 * This class is responsible for all encodings of MC system.
 * It is also responsible for variabl;e names used in SAT formula.
 */

public class SatEncoder {

    private final boolean _withTags;
    private static final Integer MAX_TAB_BITS_NUM = 3;
    private int _tagBitsNum; //number of variable used per tag
    private final int _progPointsNumberingBitsNum; //number of prog points representation bits in current SCC
    private final String _orderingType; //graph ordering method iude (for examkple ws_max_max_max)

    private SatFormulaBuilder sfb; //the formula is created using this builder object.

    public SatEncoder(final String orderingType, final boolean withTags, final int tagBitsNum,
            final int progPointsNumberingBitsNum) {
        this._withTags = withTags;
        this._tagBitsNum = tagBitsNum;
        if (SatEncoder.MAX_TAB_BITS_NUM != null) {
            this._tagBitsNum = Math.min(tagBitsNum, SatEncoder.MAX_TAB_BITS_NUM);
        }
        this._orderingType = orderingType;
        this._progPointsNumberingBitsNum = progPointsNumberingBitsNum;
    }

    // ----------------------------- Variables names ---------------------------------------
    // program point argument is in high/low set
    // part: hi. lo
    public static String progPointArgToVar(final String pointName, final int argInd, final HighLow part) {
        return pointName + "." + argInd + "-" + part;
    }

    public static String progPointArgTagVar(final String pointName, final int argInd, final int varNum) {
        return pointName + "." + argInd + "." + varNum;
    }

    // program point numbering (for bound)
    public static String progPointBoundNumberVar(final String pointName, final int bitInd) {
        return "number-b-" + pointName + "." + bitInd;
    }

    public static String[] progPointBoundNumberVars(final String pointName, final int numOfBits) {
        final String[] res = new String[numOfBits];
        for (int i = 0; i < numOfBits; i++) {
            res[i] = SatEncoder.progPointBoundNumberVar(pointName, i);
        }
        return res;
    }

    public String[] progPointBoundNumberVars(final String pointName) {
        return SatEncoder.progPointBoundNumberVars(pointName, this._progPointsNumberingBitsNum);
    }

    // program point numbering (for strict)
    public static String progPointStrictNumberVar(final String pointName, final int bitInd) {
        return "number-s-" + pointName + "." + bitInd;
    }

    public static String[] progPointStrictNumberVars(final String pointName, final int numOfBits) {
        final String[] res = new String[numOfBits];
        for (int i = 0; i < numOfBits; i++) {
            res[i] = SatEncoder.progPointStrictNumberVar(pointName, i);
        }
        return res;
    }

    public String[] progPointStrictNumberVars(final String pointName) {
        return SatEncoder.progPointStrictNumberVars(pointName, this._progPointsNumberingBitsNum);
    }

    // relationType: > or >=
    // direction: top-to-bottom, bottom-to-top, top-to,top, buttom-to-bottom
    // reversed: if true - edge toArgInd->fromArgInd with reversecd direction
    public static String mcGraphArgRelationVar(final String graphID,
        final int fromArgInd,
        final int toArgInd,
        final String direction,
        final String relationType,
        final boolean reversed) {
        if (reversed) {
            return "e_" + graphID + "_" + direction + "_" + toArgInd + relationType + fromArgInd;
        } else {
            return "e_" + graphID + "_" + direction + "_" + fromArgInd + relationType + toArgInd;
        }
    }

    // relationType: > or >=
    // direction: top-to-bottom, bottom-to-top, top-to,top, buttom-to-bottom
    public static String mcGraphArgRelationVar(final String graphID,
        final int fromArgInd,
        final int toArgInd,
        final String direction,
        final String relationType) {
        return SatEncoder.mcGraphArgRelationVar(graphID, fromArgInd, toArgInd, direction, relationType, false);
    }

    // direction: top-to-bottom, bottom-to-top, top-to,top, buttom-to-bottom
    public static String coveredByVar(final String graphID,
        final int fromArgInd,
        final int toArgInd,
        final String direction) {
        return "covered_" + graphID + "_" + direction + "_" + fromArgInd + "->" + toArgInd;
    }

    // direction: top-to-bottom, bottom-to-top, top-to,top, buttom-to-bottom
    public static String weaklyCoversVar(final String graphID, final int fromArgInd, final String direction) {
        return "weakCover_" + graphID + "_" + direction + "_" + fromArgInd;
    }

    // ordering: ws_max_max_max, ...
    public static String weakGraphOrderingVar(final String graphID, final String ordering) {
        return "weak_" + graphID + "_" + ordering;
    }

    // ordering: ws_max_max_max, ...
    public static String strictGraphOrderingVar(final String graphID, final String ordering) {
        return "strict_" + graphID + "_" + ordering;
    }

    // ordering: ws_max_max_max, ...
    public static String removableStrictGraphOrderingVar(final String graphID, final String ordering) {
        return "removableStrict_" + graphID + "_" + ordering;
    }

    // ordering: ws_max_max_max, ...
    public static String cutsetGraphVar(final String graphID, final String ordering) {
        return "cutset_" + graphID + "_" + ordering;
    }

    public static String horizontalGraphOrderingVar(final String graphID, final String ordering) {
        return "horizontal_" + graphID + "_" + ordering;
    }

    // ordering: max,min,...
    // fromPart, toPart: lo, hi
    // Ordering: tb,bt,tt,bb
    public static String weakGraphOrderingVar(final String graphID,
        final String ordering,
        final HighLow fromPart,
        final HighLow toPart,
        final String direction) {
        return "weak_" + graphID + "_" + ordering + "_" + direction + "_" + fromPart + "_" + toPart;
    }

    // ordering: max,min,...
    // fromPart, toPart: lo, hi
    // Ordering: tb,bt,tt,bb
    public static String strictGraphOrderingVar(final String graphID,
        final String ordering,
        final HighLow fromPart,
        final HighLow toPart,
        final String direction) {
        return "strict_" + graphID + "_" + ordering + "_" + direction + "_" + fromPart + "_" + toPart;
    }

    // ----------------------------- Variables names (end) ---------------------------------------

    // ----------------------------- Tupple orderings ---------------------------------------
    private void encodeGraphPart(final MCGraph mcg,
        final String ordering,
        final String direction,
        final HighLow fromPart,
        final HighLow toPart) {
        if (ordering.equals(Constants.MAX_ORDERING)) {
            this.encodeMCGraphDirectionMax(mcg, direction, fromPart, toPart);
        } else if (ordering.equals(Constants.MIN_ORDERING)) {
            this.encodeMCGraphDirectionMin(mcg, direction, fromPart, toPart);
        } else if (ordering.equals(Constants.MS_ORDERING)) {
            this.encodeMCGraphDirectionMS(mcg, direction, fromPart, toPart);
        } else if (ordering.equals(Constants.DMS_ORDERING)) {
            this.encodeMCGraphDirectionDMS(mcg, direction, fromPart, toPart);
        } else if (ordering.equals(Constants.MAX_GT_MIN_ORDERING)) {
            this.encodeMCGraphDirectionMaxGtMin(mcg, direction, fromPart, toPart);
        } else if (ordering.equals(Constants.MIN_GT_MAX_ORDERING)) {
            this.encodeMCGraphDirectionMinGtMax(mcg, direction, fromPart, toPart);
        } else {
            throw new RuntimeException("Illegal ordering: " + ordering + ".");
        }
    }

    private void tripleOrderingCommonPart(final MCGraph mcg,
        final String ordering,
        final String orderingLo,
        final String orderingHi,
        final String orderingTop) {
        final String topHiTopLoWeakVar =
            SatEncoder.weakGraphOrderingVar(mcg.getID(), orderingTop, Constants.HighLow.HIGH, Constants.HighLow.LOW,
                Constants.TOP_TO_TOP);
        final String strictOrderingVar = SatEncoder.strictGraphOrderingVar(mcg.getID(), ordering);
        final String removableStrictOrderingVar = SatEncoder.removableStrictGraphOrderingVar(mcg.getID(), ordering);

        final String pointFromID = mcg.getPointFrom().getID();
        final String pointToID = mcg.getPointTo().getID();

        final String[] pointBoundFromNumberingVars = this.progPointBoundNumberVars(pointFromID);
        final String[] pointBoundToNumberingVars = this.progPointBoundNumberVars(pointToID);

        final String[] pointStrictFromNumberingVars = this.progPointStrictNumberVars(pointFromID);
        final String[] pointStrictToNumberingVars = this.progPointStrictNumberVars(pointToID);

        String numToGTnumFromBoundVar = null;
        String numToNEQnumFromBoundVar = null;
        String numToGTnumFromStrictVar = null;
        String numToNEQnumFromStrictVar = null;

        if (Config.NUMBERS_ENCODING.equals(Constants.UnaryBinary.UNARY)) {
            numToGTnumFromBoundVar = this.sfb.iffUnaryGTTseitin(pointBoundToNumberingVars, pointBoundFromNumberingVars);
            numToNEQnumFromBoundVar =
                this.sfb.iffUnaryNEQTseitin(pointBoundToNumberingVars, pointBoundFromNumberingVars);
            if (Config.CUTSET_METHOD_2) {
                numToGTnumFromStrictVar =
                    this.sfb.iffUnaryGTTseitin(pointStrictToNumberingVars, pointStrictFromNumberingVars);
                numToNEQnumFromStrictVar =
                    this.sfb.iffUnaryNEQTseitin(pointStrictToNumberingVars, pointStrictFromNumberingVars);
            }
        } else if (Config.NUMBERS_ENCODING.equals(Constants.UnaryBinary.BINARY)) {
            numToGTnumFromBoundVar =
                this.sfb.iffBinaryGTTseitin(pointBoundToNumberingVars, pointBoundFromNumberingVars);
            numToNEQnumFromBoundVar =
                this.sfb.iffBinaryNEQTseitin(pointBoundToNumberingVars, pointBoundFromNumberingVars);
            if (Config.CUTSET_METHOD_2) {
                numToGTnumFromStrictVar =
                    this.sfb.iffBinaryGTTseitin(pointStrictToNumberingVars, pointStrictFromNumberingVars);
                numToNEQnumFromStrictVar =
                    this.sfb.iffBinaryNEQTseitin(pointStrictToNumberingVars, pointStrictFromNumberingVars);
            }
        }

        final String cutsetVar = SatEncoder.cutsetGraphVar(mcg.getID(), ordering);
        this.sfb.arrowOperator(numToGTnumFromBoundVar, cutsetVar);
        this.sfb.arrowOperator(cutsetVar, topHiTopLoWeakVar);

        //strict -> k(p)!=k(q) v cutset

        // ----- removableStrict <-> strict ^ (k(p)!=k(q) v cutset) -----
        // kpNeqKqAndCutsetVar <-> k(p)!=k(q) v cutset
        final String[] kpNeqKqOrCutsetArgs = {numToNEQnumFromBoundVar, cutsetVar };
        final String kpNeqKqOrCutsetVar = this.sfb.iffOrOperatorTseitin(kpNeqKqOrCutsetArgs);

        if (!Config.CUTSET_METHOD_2) {
            // removableStrict <-> strict ^ kpNeqKqAndCutsetVar
            final String[] removabeIffStrictAndOtherArgs = {strictOrderingVar, kpNeqKqOrCutsetVar };
            this.sfb.iffAndOperator(removableStrictOrderingVar, removabeIffStrictAndOtherArgs);
        } else {
            // kpNeqKqAndStrictVar <-> num2(p)!=num2(q) v str4ict
            final String[] kpNeqKqOrStrictArgs = {numToNEQnumFromStrictVar, strictOrderingVar };
            final String kpNeqKqOrStrictVar = this.sfb.iffOrOperatorTseitin(kpNeqKqOrStrictArgs);

            final String[] removabeIffStrictAndOtherArgs = {kpNeqKqOrStrictVar, kpNeqKqOrCutsetVar };
            this.sfb.iffAndOperator(removableStrictOrderingVar, removabeIffStrictAndOtherArgs);
        }
    }

    // ordering: ordering type
    // orderingLo: bottom-low -> top-lo
    // orderingHi: top-hi -> bottom-hi
    // ordering-top: top-hi -> top-lo
    private void tripleOrderingStrictIncWeakDec(final MCGraph mcg,
        final String ordering,
        final String orderingLo,
        final String orderingHi,
        final String orderingTop) {
        if (Config.LOG_ENCODING)
         {
            Logger.writeDebug("StrictInc: " + ordering + " " + orderingLo + " " + orderingHi + " " + orderingTop); //D
        }

        final String lowBottomUpWeakVar =
            SatEncoder.weakGraphOrderingVar(mcg.getID(), orderingLo, Constants.HighLow.LOW, Constants.HighLow.LOW,
                Constants.BOTTOM_TO_TOP);
        final String lowBottomUpStrictVar =
            SatEncoder.strictGraphOrderingVar(mcg.getID(), orderingLo, Constants.HighLow.LOW, Constants.HighLow.LOW,
                Constants.BOTTOM_TO_TOP);
        final String highTopDownWeakVar =
            SatEncoder.weakGraphOrderingVar(mcg.getID(), orderingHi, Constants.HighLow.HIGH, Constants.HighLow.HIGH,
                Constants.TOP_TO_BOTTOM);
        final String topHiTopLoWeakVar =
            SatEncoder.weakGraphOrderingVar(mcg.getID(), orderingTop, Constants.HighLow.HIGH, Constants.HighLow.LOW,
                Constants.TOP_TO_TOP);

        this.encodeGraphPart(mcg, orderingLo, Constants.BOTTOM_TO_TOP, Constants.HighLow.LOW, Constants.HighLow.LOW);
        this.encodeGraphPart(mcg, orderingHi, Constants.TOP_TO_BOTTOM, Constants.HighLow.HIGH, Constants.HighLow.HIGH);
        this.encodeGraphPart(mcg, orderingTop, Constants.TOP_TO_TOP, Constants.HighLow.HIGH, Constants.HighLow.LOW);

        //weak
        final String weakOrderingVar = SatEncoder.weakGraphOrderingVar(mcg.getID(), ordering);
        final String[] weakOrderingComponentsVars = {lowBottomUpWeakVar, highTopDownWeakVar };
        this.sfb.iffAndOperator(weakOrderingVar, weakOrderingComponentsVars);

        //strict
        final String strictOrderingVar = SatEncoder.strictGraphOrderingVar(mcg.getID(), ordering);
        final String removableStrictOrderingVar = SatEncoder.removableStrictGraphOrderingVar(mcg.getID(), ordering);

        final String[] strictOrderingComponentsVars_old =
            {lowBottomUpStrictVar, highTopDownWeakVar, topHiTopLoWeakVar }; //strict old
        final String[] strictOrderingComponentsVars_new = {lowBottomUpStrictVar, highTopDownWeakVar }; //new with cutset
        String[] strictOrderingComponentsVars;
        if (Config.CUTSET_METHOD) {
            strictOrderingComponentsVars = strictOrderingComponentsVars_new;
        } else {
            strictOrderingComponentsVars = strictOrderingComponentsVars_old;
        }
        this.sfb.iffAndOperator(strictOrderingVar, strictOrderingComponentsVars);

        if (Config.CUTSET_METHOD) {
            this.tripleOrderingCommonPart(mcg, ordering, orderingLo, orderingHi, orderingTop);
        } else {
            this.sfb.iffOperator(removableStrictOrderingVar, strictOrderingVar);
        }
    }

    // ordering: ordering type
    // orderingLo: bottom-low -> top-lo
    // orderingHi: top-hi -> bottom-hi
    // ordering-top: top-hi -> top-lo
    private void tripleOrderingWeakIncStrictDec(final MCGraph mcg,
        final String ordering,
        final String orderingLo,
        final String orderingHi,
        final String orderingTop) {
        if (Config.LOG_ENCODING)
         {
            Logger.writeDebug("WeakInc: " + ordering + " " + orderingLo + " " + orderingHi + " " + orderingTop); //D
        }

        final String lowBottomUpWeakVar =
            SatEncoder.weakGraphOrderingVar(mcg.getID(), orderingLo, Constants.HighLow.LOW, Constants.HighLow.LOW,
                Constants.BOTTOM_TO_TOP);
        final String highTopDownWeakVar =
            SatEncoder.weakGraphOrderingVar(mcg.getID(), orderingHi, Constants.HighLow.HIGH, Constants.HighLow.HIGH,
                Constants.TOP_TO_BOTTOM);
        final String highTopDownStrictVar =
            SatEncoder.strictGraphOrderingVar(mcg.getID(), orderingHi, Constants.HighLow.HIGH, Constants.HighLow.HIGH,
                Constants.TOP_TO_BOTTOM);
        final String topHiTopLoWeakVar =
            SatEncoder.weakGraphOrderingVar(mcg.getID(), orderingTop, Constants.HighLow.HIGH, Constants.HighLow.LOW,
                Constants.TOP_TO_TOP);

        this.encodeGraphPart(mcg, orderingLo, Constants.BOTTOM_TO_TOP, Constants.HighLow.LOW, Constants.HighLow.LOW);
        this.encodeGraphPart(mcg, orderingHi, Constants.TOP_TO_BOTTOM, Constants.HighLow.HIGH, Constants.HighLow.HIGH);
        this.encodeGraphPart(mcg, orderingTop, Constants.TOP_TO_TOP, Constants.HighLow.HIGH, Constants.HighLow.LOW);

        //weak
        final String weakOrderingVar = SatEncoder.weakGraphOrderingVar(mcg.getID(), ordering);
        final String[] weakOrderingComponentsVars = {lowBottomUpWeakVar, highTopDownWeakVar };
        this.sfb.iffAndOperator(weakOrderingVar, weakOrderingComponentsVars);

        //strict
        final String strictOrderingVar = SatEncoder.strictGraphOrderingVar(mcg.getID(), ordering);
        final String removableStrictOrderingVar = SatEncoder.removableStrictGraphOrderingVar(mcg.getID(), ordering);

        final String[] strictOrderingComponentsVars_old =
            {lowBottomUpWeakVar, highTopDownStrictVar, topHiTopLoWeakVar };
        ; //strict old
        final String[] strictOrderingComponentsVars_new = {lowBottomUpWeakVar, highTopDownStrictVar }; //new with cutset
        String[] strictOrderingComponentsVars;
        if (Config.CUTSET_METHOD) {
            strictOrderingComponentsVars = strictOrderingComponentsVars_new;
        } else {
            strictOrderingComponentsVars = strictOrderingComponentsVars_old;
        }
        this.sfb.iffAndOperator(strictOrderingVar, strictOrderingComponentsVars);

        if (Config.CUTSET_METHOD) {
            this.tripleOrderingCommonPart(mcg, ordering, orderingLo, orderingHi, orderingTop);
        } else {
            this.sfb.iffOperator(removableStrictOrderingVar, strictOrderingVar);
        }
    }

    private void maxOrdering(final MCGraph mcg) {
        final String graphOrdsering = Constants.GRAPH_MAX_ORDERING;
        final String strictOrderingVar = SatEncoder.strictGraphOrderingVar(mcg.getID(), graphOrdsering);
        final String weakOrderingVar = SatEncoder.weakGraphOrderingVar(mcg.getID(), graphOrdsering);

        final HighLow fromPart = Constants.HighLow.HIGH;
        final HighLow toPart = Constants.HighLow.HIGH;
        final String direction = Constants.TOP_TO_BOTTOM;
        final String ordering = Constants.MAX_ORDERING;
        this.encodeMCGraphDirectionMax(mcg, direction, fromPart, toPart);
        final String highTopDownMaxStrictVar =
            SatEncoder.strictGraphOrderingVar(mcg.getID(), ordering, fromPart, toPart, direction);
        final String highTopDownMaxWeakVar = SatEncoder.weakGraphOrderingVar(mcg.getID(), ordering, fromPart, toPart, direction);

        final String[] strictOrderingComponentsVars = {highTopDownMaxStrictVar };
        this.sfb.iffAndOperator(strictOrderingVar, strictOrderingComponentsVars);
        final String[] weakOrderingComponentsVars = {highTopDownMaxWeakVar };
        this.sfb.iffAndOperator(weakOrderingVar, weakOrderingComponentsVars);

    }

    private void minOrdering(final MCGraph mcg) {
        final String graphOrdsering = Constants.GRAPH_MIN_ORDERING;
        final String strictOrderingVar = SatEncoder.strictGraphOrderingVar(mcg.getID(), graphOrdsering);
        final String weakOrderingVar = SatEncoder.weakGraphOrderingVar(mcg.getID(), graphOrdsering);

        final HighLow fromPart = Constants.HighLow.HIGH;
        final HighLow toPart = Constants.HighLow.HIGH;
        final String direction = Constants.TOP_TO_BOTTOM;

        final String ordering = Constants.MIN_ORDERING;
        this.encodeMCGraphDirectionMin(mcg, direction, fromPart, toPart);
        final String highTopDownMinStrictVar =
            SatEncoder.strictGraphOrderingVar(mcg.getID(), ordering, fromPart, toPart, direction);
        final String highTopDownMinWeakVar = SatEncoder.weakGraphOrderingVar(mcg.getID(), ordering, fromPart, toPart, direction);

        final String[] strictOrderingComponentsVars = {highTopDownMinStrictVar };
        this.sfb.iffAndOperator(strictOrderingVar, strictOrderingComponentsVars);
        final String[] weakOrderingComponentsVars = {highTopDownMinWeakVar };
        this.sfb.iffAndOperator(weakOrderingVar, weakOrderingComponentsVars);
    }

    private void msOrdering(final MCGraph mcg) {
        final String graphOrdsering = Constants.GRAPH_MS_ORDERING;
        final String strictOrderingVar = SatEncoder.strictGraphOrderingVar(mcg.getID(), graphOrdsering);
        final String weakOrderingVar = SatEncoder.weakGraphOrderingVar(mcg.getID(), graphOrdsering);

        final HighLow fromPart = Constants.HighLow.HIGH;
        final HighLow toPart = Constants.HighLow.HIGH;
        final String direction = Constants.TOP_TO_BOTTOM;
        final String ordering = Constants.MS_ORDERING;
        this.encodeMCGraphDirectionMS(mcg, direction, fromPart, toPart);
        final String highTopDownMsStrictVar =
            SatEncoder.strictGraphOrderingVar(mcg.getID(), ordering, fromPart, toPart, direction);
        final String highTopDownMsWeakVar = SatEncoder.weakGraphOrderingVar(mcg.getID(), ordering, fromPart, toPart, direction);

        final String[] strictOrderingComponentsVars = {highTopDownMsStrictVar };
        this.sfb.iffAndOperator(strictOrderingVar, strictOrderingComponentsVars);
        final String[] weakOrderingComponentsVars = {highTopDownMsWeakVar };
        this.sfb.iffAndOperator(weakOrderingVar, weakOrderingComponentsVars);
    }

    private void dmsOrdering(final MCGraph mcg) {
        final String graphOrdsering = Constants.GRAPH_DMS_ORDERING;
        final String strictOrderingVar = SatEncoder.strictGraphOrderingVar(mcg.getID(), graphOrdsering);
        final String weakOrderingVar = SatEncoder.weakGraphOrderingVar(mcg.getID(), graphOrdsering);

        final HighLow fromPart = Constants.HighLow.HIGH;
        final HighLow toPart = Constants.HighLow.HIGH;
        final String direction = Constants.TOP_TO_BOTTOM;
        final String ordering = Constants.DMS_ORDERING;
        this.encodeMCGraphDirectionDMS(mcg, direction, fromPart, toPart);
        final String highTopDownDmsStrictVar =
            SatEncoder.strictGraphOrderingVar(mcg.getID(), ordering, fromPart, toPart, direction);
        final String highTopDownDmsWeakVar = SatEncoder.weakGraphOrderingVar(mcg.getID(), ordering, fromPart, toPart, direction);

        final String[] strictOrderingComponentsVars = {highTopDownDmsStrictVar };
        this.sfb.iffAndOperator(strictOrderingVar, strictOrderingComponentsVars);
        final String[] weakOrderingComponentsVars = {highTopDownDmsWeakVar };
        this.sfb.iffAndOperator(weakOrderingVar, weakOrderingComponentsVars);
    }

    private void maxMaxMaxOrderingStrictIncWeakDec(final MCGraph mcg) {
        this.tripleOrderingStrictIncWeakDec(mcg, Constants.GRAPH_SW_MAX_MAX_MAX_ORDERING, Constants.MAX_ORDERING,
            Constants.MAX_ORDERING, Constants.MAX_ORDERING);
    }

    private void maxMaxMaxOrderingWeakIncStrictDec(final MCGraph mcg) {
        this.tripleOrderingWeakIncStrictDec(mcg, Constants.GRAPH_WS_MAX_MAX_MAX_ORDERING, Constants.MAX_ORDERING,
            Constants.MAX_ORDERING, Constants.MAX_ORDERING);
    }

    private void msMsMaxOrderingStrictIncWeakDec(final MCGraph mcg) {
        this.tripleOrderingStrictIncWeakDec(mcg, Constants.GRAPH_SW_MS_MS_MAX_ORDERING, Constants.MS_ORDERING,
            Constants.MS_ORDERING, Constants.MAX_ORDERING);
    }

    private void msMsMaxOrderingWeakIncStrictDec(final MCGraph mcg) {
        this.tripleOrderingWeakIncStrictDec(mcg, Constants.GRAPH_WS_MS_MS_MAX_ORDERING, Constants.MS_ORDERING,
            Constants.MS_ORDERING, Constants.MAX_ORDERING);
    }

    private void msMaxMaxOrderingStrictIncWeakDec(final MCGraph mcg) {
        this.tripleOrderingStrictIncWeakDec(mcg, Constants.GRAPH_SW_MS_MAX_MAX_ORDERING, Constants.MS_ORDERING,
            Constants.MAX_ORDERING, Constants.MAX_ORDERING);
    }

    private void msMaxMaxOrderingWeakIncStrictDec(final MCGraph mcg) {
        this.tripleOrderingWeakIncStrictDec(mcg, Constants.GRAPH_WS_MS_MAX_MAX_ORDERING, Constants.MS_ORDERING,
            Constants.MAX_ORDERING, Constants.MAX_ORDERING);
    }

    private void maxMsMaxOrderingStrictIncWeakDec(final MCGraph mcg) {
        this.tripleOrderingStrictIncWeakDec(mcg, Constants.GRAPH_SW_MAX_MS_MAX_ORDERING, Constants.MAX_ORDERING,
            Constants.MS_ORDERING, Constants.MAX_ORDERING);
    }

    private void maxMsMaxOrderingWeakIncStrictDec(final MCGraph mcg) {
        this.tripleOrderingWeakIncStrictDec(mcg, Constants.GRAPH_WS_MAX_MS_MAX_ORDERING, Constants.MAX_ORDERING,
            Constants.MS_ORDERING, Constants.MAX_ORDERING);
    }

    private void dmsMaxMaxOrderingStrictIncWeakDec(final MCGraph mcg) {
        this.tripleOrderingStrictIncWeakDec(mcg, Constants.GRAPH_SW_DMS_MAX_MAX_ORDERING, Constants.DMS_ORDERING,
            Constants.MAX_ORDERING, Constants.MAX_ORDERING);
    }

    private void dmsMaxMaxOrderingWeakIncStrictDec(final MCGraph mcg) {
        this.tripleOrderingWeakIncStrictDec(mcg, Constants.GRAPH_WS_DMS_MAX_MAX_ORDERING, Constants.DMS_ORDERING,
            Constants.MAX_ORDERING, Constants.MAX_ORDERING);
    }

    private void minMinMinOrderingStrictIncWeakDec(final MCGraph mcg) {
        this.tripleOrderingStrictIncWeakDec(mcg, Constants.GRAPH_SW_MIN_MIN_MIN_ORDERING, Constants.MIN_ORDERING,
            Constants.MIN_ORDERING, Constants.MIN_ORDERING);
    }

    private void minMinMinOrderingWeakIncStrictDec(final MCGraph mcg) {
        this.tripleOrderingWeakIncStrictDec(mcg, Constants.GRAPH_WS_MIN_MIN_MIN_ORDERING, Constants.MIN_ORDERING,
            Constants.MIN_ORDERING, Constants.MIN_ORDERING);
    }

    private void minMaxMaxminOrderingStrictIncWeakDec(final MCGraph mcg) {
        this.tripleOrderingStrictIncWeakDec(mcg, Constants.GRAPH_SW_MIN_MAX_MAXMIN_ORDERING, Constants.MIN_ORDERING,
            Constants.MAX_ORDERING, Constants.MAX_GT_MIN_ORDERING);
    }

    private void minMaxMaxminOrderingWeakIncStrictDec(final MCGraph mcg) {
        this.tripleOrderingWeakIncStrictDec(mcg, Constants.GRAPH_WS_MIN_MAX_MAXMIN_ORDERING, Constants.MIN_ORDERING,
            Constants.MAX_ORDERING, Constants.MAX_GT_MIN_ORDERING);
    }

    private void minMsMaxminOrderingStrictIncWeakDec(final MCGraph mcg) {
        this.tripleOrderingStrictIncWeakDec(mcg, Constants.GRAPH_SW_MIN_MS_MAXMIN_ORDERING, Constants.MIN_ORDERING,
            Constants.MS_ORDERING, Constants.MAX_GT_MIN_ORDERING);
    }

    private void minMsMaxminOrderingWeakIncStrictDec(final MCGraph mcg) {
        this.tripleOrderingWeakIncStrictDec(mcg, Constants.GRAPH_WS_MIN_MS_MAXMIN_ORDERING, Constants.MIN_ORDERING,
            Constants.MS_ORDERING, Constants.MAX_GT_MIN_ORDERING);
    }

    private void maxMinMinmaxOrderingStrictIncWeakDec(final MCGraph mcg) {
        this.tripleOrderingStrictIncWeakDec(mcg, Constants.GRAPH_SW_MAX_MIN_MINMAX_ORDERING, Constants.MAX_ORDERING,
            Constants.MIN_ORDERING, Constants.MIN_GT_MAX_ORDERING);
    }

    private void maxMinMinmaxOrderingWeakIncStrictDec(final MCGraph mcg) {
        this.tripleOrderingWeakIncStrictDec(mcg, Constants.GRAPH_WS_MAX_MIN_MINMAX_ORDERING, Constants.MAX_ORDERING,
            Constants.MIN_ORDERING, Constants.MIN_GT_MAX_ORDERING);
    }

    private void msMinMinmaxOrderingStrictIncWeakDec(final MCGraph mcg) {
        this.tripleOrderingStrictIncWeakDec(mcg, Constants.GRAPH_SW_MS_MIN_MINMAX_ORDERING, Constants.MS_ORDERING,
            Constants.MIN_ORDERING, Constants.MIN_GT_MAX_ORDERING);
    }

    private void msMinMinmaxOrderingWeakIncStrictDec(final MCGraph mcg) {
        this.tripleOrderingWeakIncStrictDec(mcg, Constants.GRAPH_WS_MS_MIN_MINMAX_ORDERING, Constants.MS_ORDERING,
            Constants.MIN_ORDERING, Constants.MIN_GT_MAX_ORDERING);
    }

    private void dmsMinMinmaxOrderingStrictIncWeakDec(final MCGraph mcg) {
        this.tripleOrderingStrictIncWeakDec(mcg, Constants.GRAPH_SW_DMS_MIN_MINMAX_ORDERING, Constants.DMS_ORDERING,
            Constants.MIN_ORDERING, Constants.MIN_GT_MAX_ORDERING);
    }

    private void dmsMinMinmaxOrderingWeakIncStrictDec(final MCGraph mcg) {
        this.tripleOrderingWeakIncStrictDec(mcg, Constants.GRAPH_WS_DMS_MIN_MINMAX_ORDERING, Constants.DMS_ORDERING,
            Constants.MIN_ORDERING, Constants.MIN_GT_MAX_ORDERING);
    }

    private void maxMsMinmaxOrderingStrictIncWeakDec(final MCGraph mcg) {
        this.tripleOrderingStrictIncWeakDec(mcg, Constants.GRAPH_SW_MAX_MS_MINMAX_ORDERING, Constants.MAX_ORDERING,
            Constants.MS_ORDERING, Constants.MIN_GT_MAX_ORDERING);
    }

    private void maxMsMinmaxOrderingWeakIncStrictDec(final MCGraph mcg) {
        this.tripleOrderingWeakIncStrictDec(mcg, Constants.GRAPH_WS_MAX_MS_MINMAX_ORDERING, Constants.MAX_ORDERING,
            Constants.MS_ORDERING, Constants.MIN_GT_MAX_ORDERING);
    }

    private void maxDmsMinmaxOrderingStrictIncWeakDec(final MCGraph mcg) {
        this.tripleOrderingStrictIncWeakDec(mcg, Constants.GRAPH_SW_MAX_DMS_MINMAX_ORDERING, Constants.MAX_ORDERING,
            Constants.DMS_ORDERING, Constants.MIN_GT_MAX_ORDERING);
    }

    private void maxDmsMinmaxOrderingWeakIncStrictDec(final MCGraph mcg) {
        this.tripleOrderingWeakIncStrictDec(mcg, Constants.GRAPH_WS_MAX_DMS_MINMAX_ORDERING, Constants.MAX_ORDERING,
            Constants.DMS_ORDERING, Constants.MIN_GT_MAX_ORDERING);
    }

    private void minMsMinOrderingStrictIncWeakDec(final MCGraph mcg) {
        this.tripleOrderingStrictIncWeakDec(mcg, Constants.GRAPH_SW_MIN_MS_MIN_ORDERING, Constants.MIN_ORDERING,
            Constants.MS_ORDERING, Constants.MIN_ORDERING);
    }

    private void minMsMinOrderingWeakIncStrictDec(final MCGraph mcg) {
        this.tripleOrderingWeakIncStrictDec(mcg, Constants.GRAPH_WS_MIN_MS_MIN_ORDERING, Constants.MIN_ORDERING,
            Constants.MS_ORDERING, Constants.MIN_ORDERING);
    }

    private void minDmsMinOrderingStrictIncWeakDec(final MCGraph mcg) {
        this.tripleOrderingStrictIncWeakDec(mcg, Constants.GRAPH_SW_MIN_DMS_MIN_ORDERING, Constants.MIN_ORDERING,
            Constants.DMS_ORDERING, Constants.MIN_ORDERING);
    }

    private void minDmsMinOrderingWeakIncStrictDec(final MCGraph mcg) {
        this.tripleOrderingWeakIncStrictDec(mcg, Constants.GRAPH_WS_MIN_DMS_MIN_ORDERING, Constants.MIN_ORDERING,
            Constants.DMS_ORDERING, Constants.MIN_ORDERING);
    }

    // ----------------------------- Tuple orderings (end) ---------------------------------------

    private void encodeMCGraph(final MCGraph mcg) {
        // encode edges between arguments
        this.allArgsRelations(mcg);

        //max/ms , max/ms
        if (this._orderingType.equals(Constants.GRAPH_SW_MAX_MAX_MAX_ORDERING)) {
            this.maxMaxMaxOrderingStrictIncWeakDec(mcg);
        } else if (this._orderingType.equals(Constants.GRAPH_WS_MAX_MAX_MAX_ORDERING)) {
            this.maxMaxMaxOrderingWeakIncStrictDec(mcg);
        } else if (this._orderingType.equals(Constants.GRAPH_SW_MS_MS_MAX_ORDERING)) {
            this.msMsMaxOrderingStrictIncWeakDec(mcg);
        } else if (this._orderingType.equals(Constants.GRAPH_WS_MS_MS_MAX_ORDERING)) {
            this.msMsMaxOrderingWeakIncStrictDec(mcg);
        } else if (this._orderingType.equals(Constants.GRAPH_SW_MS_MAX_MAX_ORDERING)) {
            this.msMaxMaxOrderingStrictIncWeakDec(mcg);
        } else if (this._orderingType.equals(Constants.GRAPH_WS_MS_MAX_MAX_ORDERING)) {
            this.msMaxMaxOrderingWeakIncStrictDec(mcg);
        } else if (this._orderingType.equals(Constants.GRAPH_SW_MAX_MS_MAX_ORDERING)) {
            this.maxMsMaxOrderingStrictIncWeakDec(mcg);
        } else if (this._orderingType.equals(Constants.GRAPH_WS_MAX_MS_MAX_ORDERING)) {
            this.maxMsMaxOrderingWeakIncStrictDec(mcg);
        } else if (this._orderingType.equals(Constants.GRAPH_SW_DMS_MAX_MAX_ORDERING)) {
            this.dmsMaxMaxOrderingStrictIncWeakDec(mcg);
        } else if (this._orderingType.equals(Constants.GRAPH_WS_DMS_MAX_MAX_ORDERING)) {
            this.dmsMaxMaxOrderingWeakIncStrictDec(mcg);
        } else if (this._orderingType.equals(Constants.GRAPH_SW_MIN_MIN_MIN_ORDERING)) {
            this.minMinMinOrderingStrictIncWeakDec(mcg);
        } else if (this._orderingType.equals(Constants.GRAPH_WS_MIN_MIN_MIN_ORDERING)) {
            this.minMinMinOrderingWeakIncStrictDec(mcg);
        } else if (this._orderingType.equals(Constants.GRAPH_SW_MIN_MAX_MAXMIN_ORDERING)) {
            this.minMaxMaxminOrderingStrictIncWeakDec(mcg);
        } else if (this._orderingType.equals(Constants.GRAPH_WS_MIN_MAX_MAXMIN_ORDERING)) {
            this.minMaxMaxminOrderingWeakIncStrictDec(mcg);
        } else if (this._orderingType.equals(Constants.GRAPH_SW_MIN_MS_MAXMIN_ORDERING)) {
            this.minMsMaxminOrderingStrictIncWeakDec(mcg);
        } else if (this._orderingType.equals(Constants.GRAPH_WS_MIN_MS_MAXMIN_ORDERING)) {
            this.minMsMaxminOrderingWeakIncStrictDec(mcg);
        } else if (this._orderingType.equals(Constants.GRAPH_SW_MAX_MIN_MINMAX_ORDERING)) {
            this.maxMinMinmaxOrderingStrictIncWeakDec(mcg);
        } else if (this._orderingType.equals(Constants.GRAPH_WS_MAX_MIN_MINMAX_ORDERING)) {
            this.maxMinMinmaxOrderingWeakIncStrictDec(mcg);
        } else if (this._orderingType.equals(Constants.GRAPH_SW_MS_MIN_MINMAX_ORDERING)) {
            this.msMinMinmaxOrderingStrictIncWeakDec(mcg);
        } else if (this._orderingType.equals(Constants.GRAPH_WS_MS_MIN_MINMAX_ORDERING)) {
            this.msMinMinmaxOrderingWeakIncStrictDec(mcg);
        } else if (this._orderingType.equals(Constants.GRAPH_SW_DMS_MIN_MINMAX_ORDERING)) {
            this.dmsMinMinmaxOrderingStrictIncWeakDec(mcg);
        } else if (this._orderingType.equals(Constants.GRAPH_WS_DMS_MIN_MINMAX_ORDERING)) {
            this.dmsMinMinmaxOrderingWeakIncStrictDec(mcg);
        } else if (this._orderingType.equals(Constants.GRAPH_SW_MAX_MS_MINMAX_ORDERING)) {
            this.maxMsMinmaxOrderingStrictIncWeakDec(mcg);
        } else if (this._orderingType.equals(Constants.GRAPH_WS_MAX_MS_MINMAX_ORDERING)) {
            this.maxMsMinmaxOrderingWeakIncStrictDec(mcg);
        } else if (this._orderingType.equals(Constants.GRAPH_SW_MAX_DMS_MINMAX_ORDERING)) {
            this.maxDmsMinmaxOrderingStrictIncWeakDec(mcg);
        } else if (this._orderingType.equals(Constants.GRAPH_WS_MAX_DMS_MINMAX_ORDERING)) {
            this.maxDmsMinmaxOrderingWeakIncStrictDec(mcg);
        } else if (this._orderingType.equals(Constants.GRAPH_SW_MIN_MS_MIN_ORDERING)) {
            this.minMsMinOrderingStrictIncWeakDec(mcg);
        } else if (this._orderingType.equals(Constants.GRAPH_WS_MIN_MS_MIN_ORDERING)) {
            this.minMsMinOrderingWeakIncStrictDec(mcg);
        } else if (this._orderingType.equals(Constants.GRAPH_SW_MIN_DMS_MIN_ORDERING)) {
            this.minDmsMinOrderingStrictIncWeakDec(mcg);
        } else if (this._orderingType.equals(Constants.GRAPH_WS_MIN_DMS_MIN_ORDERING)) {
            this.minDmsMinOrderingWeakIncStrictDec(mcg);
        } else if (this._orderingType.equals(Constants.GRAPH_MAX_ORDERING)) {
            this.maxOrdering(mcg);
        } else if (this._orderingType.equals(Constants.GRAPH_MIN_ORDERING)) {
            this.minOrdering(mcg);
        } else if (this._orderingType.equals(Constants.GRAPH_MS_ORDERING)) {
            this.msOrdering(mcg);
        } else if (this._orderingType.equals(Constants.GRAPH_DMS_ORDERING)) {
            this.dmsOrdering(mcg);
        } else {
            throw new RuntimeException("Illegal ordering type: " + this._orderingType + ".");
        }

        // For debug usage: Do not filter off any argument
        if (Config.USE_ALL_ARGS) {
            final String progPointFromID = mcg.getPointFrom().getID();
            final String progPointToID = mcg.getPointTo().getID();
            for (int i = 0; i < mcg.getPointFrom().getArguments().length; i++) {
                final String[] clause = {progPointFromID + "." + i + "-lo", progPointFromID + "." + i + "-hi" };
                this.sfb.addClause(Arrays.asList(clause));
            }
            for (int i = 0; i < mcg.getPointTo().getArguments().length; i++) {
                final String[] clause = {progPointToID + "." + i + "-lo", progPointToID + "." + i + "-hi" };
                this.sfb.addClause(Arrays.asList(clause));
                // non-tuple multiset ordering
                if (this._orderingType.equals(Constants.GRAPH_MAX_ORDERING)
                    || this._orderingType.equals(Constants.GRAPH_MIN_ORDERING)
                    || this._orderingType.equals(Constants.GRAPH_MS_ORDERING)
                    || this._orderingType.equals(Constants.GRAPH_DMS_ORDERING)) {
                    this.sfb.unit(progPointToID + "." + i + "-hi");
                }
            }
        }
    }

    // assumes correct graph
    // can not be two relations between a pair of arguments (E.g. x>y and x>=y)
    // direction: top-to-top, bottom-to-top, top-to-bottom, bottom-to-bottom
    // fromPoint, toPoint: hi, lo
    // ordering: min, max
    private void encodeMCGraphDirectionMinOrMax(final MCGraph mcg,
        final String direction,
        HighLow fromPart,
        HighLow toPart,
        final String ordering) {
        final String graphID = mcg.getID();

        if (Config.LOG_ENCODING) {
            Logger.write("Encoding graph " + graphID + "; ordering=" + ordering + "; direction=" + direction + " "
                + fromPart + "->" + toPart + ":\t" + mcg);
        }

        // Use mcg program points (from and to) according to direction
        ProgramPoint pointFrom = mcg.getPointFrom();
        ProgramPoint pointTo = mcg.getPointTo();

        if (direction.equals(Constants.BOTTOM_TO_TOP) || direction.equals(Constants.BOTTOM_TO_BOTTOM)) {
            pointFrom = mcg.getPointTo();
        }
        if (direction.equals(Constants.BOTTOM_TO_TOP) || direction.equals(Constants.TOP_TO_TOP)) {
            pointTo = mcg.getPointFrom();
        }

        // final variables for strict and weak orderings
        final String strictGraphOrderingVar = SatEncoder.strictGraphOrderingVar(graphID, ordering, fromPart, toPart, direction);
        final String weakGraphOrderingVar = SatEncoder.weakGraphOrderingVar(graphID, ordering, fromPart, toPart, direction);

        boolean revertedEdges = false;
        // if the ordering is min than reverse edges and points accordingly
        if (ordering.equals(Constants.MIN_ORDERING)) {
            revertedEdges = true;
            if (direction.equals(Constants.BOTTOM_TO_TOP) || direction.equals(Constants.TOP_TO_BOTTOM)) {
                final ProgramPoint tmp = pointFrom;
                pointFrom = pointTo;
                pointTo = tmp;
            }

            if (direction.equals(Constants.TOP_TO_TOP) || direction.equals(Constants.BOTTOM_TO_BOTTOM)) {
                final HighLow tmp = fromPart;
                fromPart = toPart;
                toPart = tmp;
            }
        }

        final String fromPointID = pointFrom.getID();
        final String toPointID = pointTo.getID();

        final Argument[] argsFrom = pointFrom.getArguments();
        final Argument[] argsTo = pointTo.getArguments();

        final String[] gtTseitins = new String[argsTo.length]; //greater than
        final String[] geqTseitins = new String[argsTo.length]; // greater than / equals
        for (int j = 0; j < argsTo.length; j++) {
            final String toArgVar = SatEncoder.progPointArgToVar(toPointID, j, toPart); //==order dependent
            // e_i>j and e_i>j ^ pi
            final String[] gtVars = new String[argsFrom.length]; // greater than / equals
            final String[] gtAndFilteredVars = new String[argsFrom.length]; // greater than / equals
            // e_i>=j and e_i>=j ^ pi
            final String[] geqVars = new String[argsFrom.length]; // greater than / equals
            final String[] geqAndFilteredVars = new String[argsFrom.length]; // greater than / equals

            for (int i = 0; i < argsFrom.length; i++) {
                final String fromArgVar = SatEncoder.progPointArgToVar(fromPointID, i, fromPart); //==order dependent

                gtVars[i] = SatEncoder.mcGraphArgRelationVar(graphID, i, j, direction, ">", revertedEdges);
                gtAndFilteredVars[i] = this.sfb.andOperatorTseitin(gtVars[i], fromArgVar);
                if (Config.LOG_ENCODING) {
                    Logger.writeDebug(gtAndFilteredVars[i] + "<=> [(" + gtVars[i] + ") ^ (" + fromArgVar + ")]");
                }

                geqVars[i] = SatEncoder.mcGraphArgRelationVar(graphID, i, j, direction, ">=", revertedEdges);
                geqAndFilteredVars[i] = this.sfb.andOperatorTseitin(geqVars[i], fromArgVar);
                if (Config.LOG_ENCODING) {
                    Logger.writeDebug(geqAndFilteredVars[i] + "<=> [(" + geqVars[i] + ") ^ (" + fromArgVar + ")]");
                }
            }

            // qj -> V(e_i>j ^ pi)
            gtTseitins[j] = this.sfb.arrowOrOperator(toArgVar, gtAndFilteredVars);
            // qj -> V(e_i>=j ^ pi)
            geqTseitins[j] = this.sfb.arrowOrOperator(toArgVar, geqAndFilteredVars);
            if (Config.LOG_ENCODING) {
                Logger.writeDebug(gtTseitins[j] + " <=> " + toArgVar + " -> " + Arrays.toString(gtVars));
                Logger.writeDebug(geqTseitins[j] + " <=> " + toArgVar + " -> " + Arrays.toString(geqVars));
            }
        }

        // strict <-> ^(qj->Ve) ^ Vpi
        //        String strictGraphOrderingVar = strictGraphOrderingVar(graphID,ordering,fromPart,toPart,direction);
        final String[] fromArgsVars = new String[argsFrom.length];
        for (int i = 0; i < argsFrom.length; i++) {
            fromArgsVars[i] = SatEncoder.progPointArgToVar(fromPointID, i, fromPart); //==order dependent
        }
        final String fromArgChoosenTseitin = this.sfb.iffOrOperatorTseitin(fromArgsVars);
        if (Config.LOG_ENCODING) {
            Logger.writeDebug(fromArgChoosenTseitin + " <=> " + Arrays.toString(fromArgsVars));
        }
        final String[] strictIffRhs = new String[gtTseitins.length + 1];
        strictIffRhs[strictIffRhs.length - 1] = fromArgChoosenTseitin;
        for (int i = 0; i < gtTseitins.length; i++) {
            strictIffRhs[i] = gtTseitins[i];
        }
        this.sfb.iffAndOperator(strictGraphOrderingVar, strictIffRhs);
        if (Config.LOG_ENCODING) {
            Logger.writeDebug(strictGraphOrderingVar + " <-> " + Arrays.toString(strictIffRhs));
        }

        // weak <-> ^(qj->Ve)
        //        String weakGraphOrderingVar = weakGraphOrderingVar(graphID,ordering,fromPart,toPart,direction);
        this.sfb.iffAndOperator(weakGraphOrderingVar, geqTseitins);
        if (Config.LOG_ENCODING) {
            Logger.writeDebug(weakGraphOrderingVar + " <-> " + Arrays.toString(geqTseitins));
        }
    }

    private void encodeMCGraphDirectionMax(final MCGraph mcg,
        final String direction,
        final HighLow fromPart,
        final HighLow toPart) {
        this.encodeMCGraphDirectionMinOrMax(mcg, direction, fromPart, toPart, Constants.MAX_ORDERING);
    }

    private void encodeMCGraphDirectionMin(final MCGraph mcg,
        final String direction,
        final HighLow fromPart,
        final HighLow toPart) {
        this.encodeMCGraphDirectionMinOrMax(mcg, direction, fromPart, toPart, Constants.MIN_ORDERING);
    }

    private void encodeMCGraphDirectionMSorDMS(final MCGraph mcg,
        final String direction,
        HighLow fromPart,
        HighLow toPart,
        final String ordering) {
        final String graphID = mcg.getID();

        if (Config.LOG_ENCODING) {
            Logger.write("Encoding graph " + graphID + "; ordering=" + ordering + "; direction=" + direction + " "
                + fromPart + "->" + toPart + ":\t" + mcg);
        }

        // Use mcg program points (from and to) according to direction
        ProgramPoint pointFrom = mcg.getPointFrom();
        ProgramPoint pointTo = mcg.getPointTo();

        if (direction.equals(Constants.BOTTOM_TO_TOP) || direction.equals(Constants.BOTTOM_TO_BOTTOM)) {
            pointFrom = mcg.getPointTo();
        }
        if (direction.equals(Constants.BOTTOM_TO_TOP) || direction.equals(Constants.TOP_TO_TOP)) {
            pointTo = mcg.getPointFrom();
        }

        boolean revertedEdges = false;
        // if the ordering is dms than reverse edges and points accordingly
        if (ordering.equals(Constants.DMS_ORDERING)) {
            revertedEdges = true;
            if (direction.equals(Constants.BOTTOM_TO_TOP) || direction.equals(Constants.TOP_TO_BOTTOM)) {
                final ProgramPoint tmp = pointFrom;
                pointFrom = pointTo;
                pointTo = tmp;
            }

            if (direction.equals(Constants.TOP_TO_TOP) || direction.equals(Constants.BOTTOM_TO_BOTTOM)) {
                final HighLow tmp = fromPart;
                fromPart = toPart;
                toPart = tmp;
            }
        }

        final String fromPoint = pointFrom.getID();
        final String toPoint = pointTo.getID();
        final Argument[] argsFrom = pointFrom.getArguments();
        final Argument[] argsTo = pointTo.getArguments();

        // Line 1 in the article
        // weak <=> qj -> ^j (Vi(gamma_i_j))
        final String[] coveredVars = new String[argsTo.length];
        for (int j = 0; j < argsTo.length; j++) {
            final String toArgVar = SatEncoder.progPointArgToVar(toPoint, j, toPart);
            final String[] coveringJVars = new String[argsFrom.length];
            for (int i = 0; i < argsFrom.length; i++) {
                coveringJVars[i] = SatEncoder.coveredByVar(graphID, i, j, direction);
            }
            // tseitin <=> qj -> V(gamma_i_j)
            coveredVars[j] = this.sfb.arrowOrOperator(toArgVar, coveringJVars);
            if (Config.LOG_ENCODING) {
                Logger.writeDebug(coveredVars[j] + " <=> " + toArgVar + " -> V" + Arrays.toString(coveringJVars));
            }
        }
        final String weakGraphOrderingVar = SatEncoder.weakGraphOrderingVar(graphID, ordering, fromPart, toPart, direction);
        this.sfb.iffAndOperator(weakGraphOrderingVar, coveredVars);
        if (Config.LOG_ENCODING) {
            Logger.writeDebug(weakGraphOrderingVar + " <=> ^" + Arrays.toString(coveredVars));
        }

        // Line 2 in the article
        // strict <-> at_least_one_oversd_strictly ^ weak
        final String[] strictlyCoveringVars = new String[argsFrom.length];
        for (int i = 0; i < argsFrom.length; i++) {
            final String fromArgVar = SatEncoder.progPointArgToVar(fromPoint, i, fromPart);
            final String coveringIsStrictlyVar = CommonOperations.negateLiteral(SatEncoder.weaklyCoversVar(graphID, i, direction));
            strictlyCoveringVars[i] = this.sfb.andOperatorTseitin(fromArgVar, coveringIsStrictlyVar);
            if (Config.LOG_ENCODING) {
                Logger.writeDebug(strictlyCoveringVars[i] + " <=> " + fromArgVar + "^" + coveringIsStrictlyVar);
            }
        }
        final String oneCoversStrictlyVar = this.sfb.iffOrOperatorTseitin(strictlyCoveringVars);
        if (Config.LOG_ENCODING) {
            Logger.writeDebug(oneCoversStrictlyVar + " <=> V" + Arrays.toString(strictlyCoveringVars));
        }

        final String strictGraphOrderingVar = SatEncoder.strictGraphOrderingVar(graphID, ordering, fromPart, toPart, direction);
        // strict <-> at_least_one_oversd_strictly ^ weak
        this.sfb.andOperator(strictGraphOrderingVar, oneCoversStrictlyVar, weakGraphOrderingVar);
        if (Config.LOG_ENCODING) {
            Logger.writeDebug(strictGraphOrderingVar + " <=> " + oneCoversStrictlyVar + " ^ " + weakGraphOrderingVar);
        }

        // Line 3 in the article
        // covering_i_j -> pi^qj^e_i>=j^(-ei <-> e_i>j)
        for (int i = 0; i < argsFrom.length; i++) {
            final String fromArgVar = SatEncoder.progPointArgToVar(fromPoint, i, fromPart);
            for (int j = 0; j < argsTo.length; j++) {
                final String toArgVar = SatEncoder.progPointArgToVar(toPoint, j, toPart);

                final String coveringVar = SatEncoder.coveredByVar(graphID, i, j, direction);
                final String coveringIsWeakVar = SatEncoder.weaklyCoversVar(graphID, i, direction);

                final String weakArgsRelationVar = SatEncoder.mcGraphArgRelationVar(graphID, i, j, direction, ">=", revertedEdges);
                final String strictArgsRelationVar =
                    SatEncoder.mcGraphArgRelationVar(graphID, i, j, direction, ">", revertedEdges);

                //tseitin <=> -ei <-> e_i>j
                final String strictCoverNeedsStrintArgsRelVar =
                    this.sfb.iffTseitinOperator(CommonOperations.negateLiteral(coveringIsWeakVar),
                        strictArgsRelationVar);
                if (Config.LOG_ENCODING) {
                    Logger.writeDebug(strictCoverNeedsStrintArgsRelVar + " <=> "
                        + CommonOperations.negateLiteral(coveringIsWeakVar) + " <-> " + strictArgsRelationVar);
                }

                final String[] coveringVars =
                    {fromArgVar, toArgVar, weakArgsRelationVar, strictCoverNeedsStrintArgsRelVar };
                this.sfb.arrowAndOperator(coveringVar, coveringVars);
                if (Config.LOG_ENCODING) {
                    Logger.writeDebug(coveringVar + " -> ^" + Arrays.toString(coveringVars));
                }
            }
        }

        // Line 4 in the article
        //
        for (int i = 0; i < argsFrom.length; i++) {
            final String[] coveredByIVars = new String[argsTo.length];
            for (int j = 0; j < argsTo.length; j++) {
                coveredByIVars[j] = SatEncoder.coveredByVar(graphID, i, j, direction);
            }
            // ttseitin <=> exactlyOne(covering_j)
            final String coveringExactlyOneVar = this.sfb.exactlyOneTseitin(coveredByIVars);
            if (Config.LOG_ENCODING) {
                Logger.writeDebug(coveringExactlyOneVar + " <=> " + Arrays.toString(coveredByIVars));
            }

            final String fromArgVar = SatEncoder.progPointArgToVar(fromPoint, i, fromPart);
            final String coveringIsWeakVar = SatEncoder.weaklyCoversVar(graphID, i, direction);

            // pi -> e_i => iCoveringExactlyOne
            if (ordering.equals(Constants.MS_ORDERING) || ordering.equals(Constants.DMS_ORDERING)) {
                // a -> b -> c => {-a v -b v c}
                final String[] clause =
                    {CommonOperations.negateLiteral(fromArgVar), CommonOperations.negateLiteral(coveringIsWeakVar),
                        coveringExactlyOneVar };
                this.sfb.addClause(Arrays.asList(clause));
                if (Config.LOG_ENCODING) {
                    Logger.writeDebug(fromArgVar + " -> " + coveringIsWeakVar + " -> " + coveringExactlyOneVar);
                }
            } // pi => iCoveringExactlyOne
            else {
                throw new RuntimeException("Illegal ordering type: " + ordering + "!");
            }
        }
    }

    private void encodeMCGraphDirectionMS(final MCGraph mcg,
        final String direction,
        final HighLow fromPart,
        final HighLow toPart) {
        this.encodeMCGraphDirectionMSorDMS(mcg, direction, fromPart, toPart, Constants.MS_ORDERING);
    }

    private void encodeMCGraphDirectionDMS(final MCGraph mcg,
        final String direction,
        final HighLow fromPart,
        final HighLow toPart) {
        this.encodeMCGraphDirectionMSorDMS(mcg, direction, fromPart, toPart, Constants.DMS_ORDERING);
    }

    private void encodeMCGraphDirectionMaxGtMin(final MCGraph mcg,
        final String direction,
        final HighLow fromPart,
        final HighLow toPart) {
        final String graphID = mcg.getID();

        final String ordering = Constants.MAX_GT_MIN_ORDERING;
        if (Config.LOG_ENCODING) {
            Logger.write("Encoding graph " + graphID + "; ordering=" + ordering + "; direction=" + direction + " "
                + fromPart + "->" + toPart + ":\t" + mcg);
        }

        // Use mcg program points (from and to) according to direction
        ProgramPoint pointFrom = mcg.getPointFrom();
        ProgramPoint pointTo = mcg.getPointTo();

        if (direction.equals(Constants.BOTTOM_TO_TOP) || direction.equals(Constants.BOTTOM_TO_BOTTOM)) {
            pointFrom = mcg.getPointTo();
        }
        if (direction.equals(Constants.BOTTOM_TO_TOP) || direction.equals(Constants.TOP_TO_TOP)) {
            pointTo = mcg.getPointFrom();
        }

        final String fromPointID = pointFrom.getID();
        final String toPointID = pointTo.getID();
        final Argument[] argsFrom = pointFrom.getArguments();
        final Argument[] argsTo = pointTo.getArguments();

        final String[] weakOrdering = new String[argsFrom.length * argsTo.length];
        final String[] strictOrdering = new String[argsFrom.length * argsTo.length];
        for (int i = 0; i < argsFrom.length; i++) {
            for (int j = 0; j < argsTo.length; j++) {
                final String fromArgVar = SatEncoder.progPointArgToVar(fromPointID, i, fromPart);
                final String toArgVar = SatEncoder.progPointArgToVar(toPointID, j, toPart);
                final String weakEdgeVar = SatEncoder.mcGraphArgRelationVar(graphID, i, j, direction, ">=");
                final String strictEdgeVar = SatEncoder.mcGraphArgRelationVar(graphID, i, j, direction, ">");

                final String[] useWeakEdge = {fromArgVar, toArgVar, weakEdgeVar };
                weakOrdering[i * argsTo.length + j] = this.sfb.iffAndOperatorTseitin(useWeakEdge);

                final String[] useStrictEdge = {fromArgVar, toArgVar, strictEdgeVar };
                strictOrdering[i * argsTo.length + j] = this.sfb.iffAndOperatorTseitin(useStrictEdge);

                if (Config.LOG_ENCODING) {
                    Logger.writeDebug(weakOrdering[i * argsTo.length + j] + " <=> [" + fromArgVar + "^" + toArgVar
                        + "^" + weakEdgeVar + "]");
                    Logger.writeDebug(strictOrdering[i * argsTo.length + j] + " <=> [" + fromArgVar + "^" + toArgVar
                        + "^" + strictEdgeVar + "]");
                }
            }
        }
        final String weakGraphOrderingVar = SatEncoder.weakGraphOrderingVar(graphID, ordering, fromPart, toPart, direction);
        this.sfb.iffOrOperator(weakGraphOrderingVar, weakOrdering);

        final String strictGraphOrderingVar = SatEncoder.strictGraphOrderingVar(graphID, ordering, fromPart, toPart, direction);
        this.sfb.iffOrOperator(strictGraphOrderingVar, strictOrdering);

        if (Config.LOG_ENCODING) {
            Logger.writeDebug(weakGraphOrderingVar + " <=> V" + Arrays.toString(weakOrdering));
            Logger.writeDebug(strictGraphOrderingVar + " <=> V" + Arrays.toString(strictOrdering));
        }
    }

    private void encodeMCGraphDirectionMinGtMax(final MCGraph mcg,
        final String direction,
        final HighLow fromPart,
        final HighLow toPart) {
        final String graphID = mcg.getID();

        final String ordering = Constants.MIN_GT_MAX_ORDERING;
        if (Config.LOG_ENCODING) {
            Logger.write("Encoding graph " + graphID + "; ordering=" + ordering + "; direction=" + direction + " "
                + fromPart + "->" + toPart + ":\t" + mcg);
        }

        // Use mcg program points (from and to) according to direction
        ProgramPoint pointFrom = mcg.getPointFrom();
        ProgramPoint pointTo = mcg.getPointTo();

        if (direction.equals(Constants.BOTTOM_TO_TOP) || direction.equals(Constants.BOTTOM_TO_BOTTOM)) {
            pointFrom = mcg.getPointTo();
        }
        if (direction.equals(Constants.BOTTOM_TO_TOP) || direction.equals(Constants.TOP_TO_TOP)) {
            pointTo = mcg.getPointFrom();
        }

        final String fromPointID = pointFrom.getID();
        final String toPointID = pointTo.getID();
        final Argument[] argsFrom = pointFrom.getArguments();
        final Argument[] argsTo = pointTo.getArguments();

        final String[] weakOrdering = new String[argsFrom.length * argsTo.length];
        final String[] strictOrdering = new String[argsFrom.length * argsTo.length];
        for (int i = 0; i < argsFrom.length; i++) {
            for (int j = 0; j < argsTo.length; j++) {
                final String fromArgVar = SatEncoder.progPointArgToVar(fromPointID, i, fromPart);
                final String toArgVar = SatEncoder.progPointArgToVar(toPointID, j, toPart);
                final String weakEdgeVar = SatEncoder.mcGraphArgRelationVar(graphID, i, j, direction, ">=");
                final String strictEdgeVar = SatEncoder.mcGraphArgRelationVar(graphID, i, j, direction, ">");

                // if argGFrom and argTo are both chosen, there should be weak edge
                final String[] useWeakEdge =
                    {CommonOperations.negateLiteral(fromArgVar), CommonOperations.negateLiteral(toArgVar), weakEdgeVar };
                weakOrdering[i * argsTo.length + j] = this.sfb.iffOrOperatorTseitin(useWeakEdge);

                // if argGFrom and argTo are both chosen, there should be strict edge
                final String[] useStrictEdge =
                    {CommonOperations.negateLiteral(fromArgVar), CommonOperations.negateLiteral(toArgVar),
                        strictEdgeVar };
                strictOrdering[i * argsTo.length + j] = this.sfb.iffOrOperatorTseitin(useStrictEdge);

                if (Config.LOG_ENCODING) {
                    Logger.writeDebug(weakOrdering[i * argsTo.length + j] + " <=> ^[-" + fromArgVar + "v-" + toArgVar
                        + "v" + weakEdgeVar + "]");
                    Logger.writeDebug(strictOrdering[i * argsTo.length + j] + " <=> ^[-" + fromArgVar + "v-" + toArgVar
                        + "v" + strictEdgeVar + "]");
                }
            }
        }
        final String weakGraphOrderingVar = SatEncoder.weakGraphOrderingVar(graphID, ordering, fromPart, toPart, direction);
        this.sfb.iffAndOperator(weakGraphOrderingVar, weakOrdering);

        final String strictGraphOrderingVar = SatEncoder.strictGraphOrderingVar(graphID, ordering, fromPart, toPart, direction);
        this.sfb.iffAndOperator(strictGraphOrderingVar, strictOrdering);

        if (Config.LOG_ENCODING) {
            Logger.writeDebug(weakGraphOrderingVar + " <=> ^" + Arrays.toString(weakOrdering));
            Logger.writeDebug(strictGraphOrderingVar + " <=> ^" + Arrays.toString(strictOrdering));
        }
    }

    // ordering - the type of graph ordering
    public SatFormula encodeProgram(final List<MCGraph> mcGraphs,
        final String ordering,
        final boolean withTags,
        final int tagBitsNum) {
        this.sfb = new SatFormulaBuilder();

        // Get ProgramPoints set from the MCGraphs set
        final Set<String> programPointsIDs = new HashSet<String>();
        final Set<ProgramPoint> programPoints = new HashSet<ProgramPoint>();
        for (final MCGraph mcg : mcGraphs) {
            final ProgramPoint pointFrom = mcg.getPointFrom();
            final ProgramPoint pointTo = mcg.getPointFrom();
            if (!programPointsIDs.contains(pointFrom.getID())) {
                programPointsIDs.add(pointFrom.getID());
                programPoints.add(pointFrom);
            }
            if (!programPointsIDs.contains(pointTo.getID())) {
                programPointsIDs.add(pointTo.getID());
                programPoints.add(pointTo);
            }
        }

        // ========================= cutsets ========================
        // SCC program points numbering
        for (final ProgramPoint programPoint : programPoints) {
            final String progPointID = programPoint.getID();
            final String[] progPointBoundNumberingVars = this.progPointBoundNumberVars(progPointID);
            final String[] progPointStrictNumberingVars = this.progPointStrictNumberVars(progPointID);
            if (Config.NUMBERS_ENCODING.equals(Constants.UnaryBinary.UNARY)) {
                this.sfb.unary(progPointBoundNumberingVars);
                this.sfb.unary(progPointStrictNumberingVars);
            }
        }

        //if num(to)>num(from) the graph is in the cutset
        for (final MCGraph mcg : mcGraphs) {
            final String mcInCutsetVar = SatEncoder.cutsetGraphVar(mcg.getID(), ordering);
            final String[] progPointBoundFromVars = this.progPointBoundNumberVars(mcg.getPointFrom().getID());
            final String[] progPointBoundToVars = this.progPointBoundNumberVars(mcg.getPointTo().getID());

            final String mcStrictVar = SatEncoder.strictGraphOrderingVar(mcg.getID(), ordering);
            final String[] progPointStrictFromVars = this.progPointStrictNumberVars(mcg.getPointFrom().getID());
            final String[] progPointStrictToVars = this.progPointStrictNumberVars(mcg.getPointTo().getID());

            String toGTFromBoundVar = null;
            String toGTFromStrictVar = null;
            if (Config.NUMBERS_ENCODING.equals(Constants.UnaryBinary.UNARY)) {
                toGTFromBoundVar = this.sfb.iffUnaryGTTseitin(progPointBoundToVars, progPointBoundFromVars);
                if (Config.CUTSET_METHOD_2) {
                    toGTFromStrictVar = this.sfb.iffUnaryGTTseitin(progPointStrictToVars, progPointStrictFromVars);
                }
            } else if (Config.NUMBERS_ENCODING.equals(Constants.UnaryBinary.BINARY)) {
                toGTFromBoundVar = this.sfb.iffBinaryGTTseitin(progPointBoundToVars, progPointBoundFromVars);
                if (Config.CUTSET_METHOD_2) {
                    toGTFromStrictVar = this.sfb.iffBinaryGTTseitin(progPointStrictToVars, progPointStrictFromVars);
                }
            }

            this.sfb.arrowOperator(toGTFromBoundVar, mcInCutsetVar); //num2(p)<num2(q) -> bound
            if (Config.CUTSET_METHOD_2) {
                this.sfb.arrowOperator(toGTFromStrictVar, mcStrictVar);
            }
        }
        //cutsets end

        if (!Config.HIGH_LOW_MAY_INTERSECT || Config.HIGH_LOW_NOT_EMPTY) {
            final List<String> argsLoVars = new ArrayList<String>(); //for non-empty low/high constraints
            final List<String> argsHiVars = new ArrayList<String>();//for non-empty low/high constraints
            for (final ProgramPoint progPoint : programPoints) {
                for (int i = 0; i < progPoint.getArguments().length; i++) {
                    final String argHiVar = SatEncoder.progPointArgToVar(progPoint.getID(), i, Constants.HighLow.HIGH);
                    final String argLoVar = SatEncoder.progPointArgToVar(progPoint.getID(), i, Constants.HighLow.LOW);

                    argsHiVars.add(argHiVar);
                    argsLoVars.add(argLoVar);

                    //constraint for non-intersecting high and low sets
                    //In each program point: for each var (-var_hi v -var_lo}
                    if (!Config.HIGH_LOW_MAY_INTERSECT) {
                        final String[] atMostOne =
                            {CommonOperations.negateLiteral(argHiVar), CommonOperations.negateLiteral(argLoVar) };
                        this.sfb.addClause(Arrays.asList(atMostOne));
                        if (Config.LOG_ENCODING) {
                            Logger.writeDebug("Clause: " + Arrays.toString(atMostOne));
                        }
                    }
                }
            }

            // non-empty low/high constraints
            if (Config.HIGH_LOW_NOT_EMPTY) {
                this.sfb.addClause(argsLoVars);
                this.sfb.addClause(argsHiVars);
                if (Config.LOG_ENCODING) {
                    Logger.writeDebug("Clause: " + argsHiVars);
                    Logger.writeDebug("Clause: " + argsLoVars);
                }
            }
        }

        // encode the MC graphs
        for (final MCGraph mcGraph : mcGraphs) {
            this.encodeMCGraph(mcGraph);
        }

        // All graphs ordered weakly and at least one strictly
        final List<String> atLeastOneStrict = new ArrayList<String>();
        for (final MCGraph mcGraph : mcGraphs) {
            final String mcGraphID = mcGraph.getID();
            final String weakOrdering = SatEncoder.weakGraphOrderingVar(mcGraphID, ordering);
            final String strictOrdering = SatEncoder.removableStrictGraphOrderingVar(mcGraphID, ordering);
            this.sfb.unit(weakOrdering);
            if (Config.LOG_ENCODING) {
                Logger.writeDebug("Unit: " + weakOrdering);
            }
            atLeastOneStrict.add(strictOrdering);
        }
        this.sfb.addClause(atLeastOneStrict);
        if (Config.LOG_ENCODING) {
            Logger.writeDebug("Clause: " + atLeastOneStrict);
        }

        return this.sfb.satFormula();
    }

    // direction: top-to-bottom, bottom-to-top, top-to,top, buttom-to-buttom
    // add constraints for relation betwee arguments:
    //e>= <-> ... and e> <-> ...
    //public void argsRelation(int argFromInd, int argToInd, String relationType, String direction, String graphID, String fromPointID, String toPointID, boolean withTags, int tagBitsNum)
    public void directionArgsRelations(final MCGraph mcGraph,
        final ProgramPoint pointFrom,
        final ProgramPoint pointTo,
        final String direction) {
        final String graphID = mcGraph.getID();
        final String fromPointID = pointFrom.getID();
        final String toPointID = pointTo.getID();
        final Argument[] argsFrom = pointFrom.getArguments();
        final Argument[] argsTo = pointTo.getArguments();

        for (int argFromInd = 0; argFromInd < argsFrom.length; argFromInd++) {
            for (int argToInd = 0; argToInd < argsTo.length; argToInd++) {

                // >,  >= or null
                final String relationType = mcGraph.getRelation(argsFrom[argFromInd], argsTo[argToInd]);
                final String relationGTVar = SatEncoder.mcGraphArgRelationVar(graphID, argFromInd, argToInd, direction, ">");
                final String relationGEQVar = SatEncoder.mcGraphArgRelationVar(graphID, argFromInd, argToInd, direction, ">=");

                if ((direction.equals(Constants.TOP_TO_TOP) || direction.equals(Constants.BOTTOM_TO_BOTTOM))
                    && argFromInd == argToInd) {
                    if (!Config.HIGH_LOW_MAY_INTERSECT) {
                        // self edge
                        this.sfb.unit(CommonOperations.negateLiteral(relationGTVar));
                        if (Config.LOG_ENCODING) {
                            Logger.writeDebug("Unit1: " + CommonOperations.negateLiteral(relationGTVar));
                        }
                        this.sfb.unit(relationGEQVar);
                        if (Config.LOG_ENCODING) {
                            Logger.writeDebug("Unit1: " + relationGEQVar);
                        }
                    }
                } else if (relationType == null) { // no relation between vars
                    this.sfb.unit(CommonOperations.negateLiteral(relationGTVar));
                    if (Config.LOG_ENCODING) {
                        Logger.writeDebug("Unit: " + CommonOperations.negateLiteral(relationGTVar));
                    }
                    this.sfb.unit(CommonOperations.negateLiteral(relationGEQVar));
                    if (Config.LOG_ENCODING) {
                        Logger.writeDebug("Unit: " + CommonOperations.negateLiteral(relationGEQVar));
                    }
                } else if (relationType.equals(">")) { // both relations accure
                    this.sfb.unit(relationGTVar);
                    if (Config.LOG_ENCODING) {
                        Logger.writeDebug("Unit: " + relationGTVar);
                    }
                    this.sfb.unit(relationGEQVar);
                    if (Config.LOG_ENCODING) {
                        Logger.writeDebug("Unit: " + relationGEQVar);
                    }
                } else if (relationType.equals(">=")) { // >= occurs, > depends on tag
                    if (this._withTags) { // with tags
                        final String[] fromTagVars = new String[this._tagBitsNum];
                        final String[] toTagVars = new String[this._tagBitsNum];
                        for (int i = 0; i < this._tagBitsNum; i++) {
                            fromTagVars[i] = SatEncoder.progPointArgTagVar(fromPointID, argFromInd, i);
                            toTagVars[i] = SatEncoder.progPointArgTagVar(toPointID, argToInd, i);
                        }

                        // unary tags encoding
                        if (Config.NUMBERS_ENCODING.equals(Constants.UnaryBinary.UNARY)) {
                            this.sfb.unary(fromTagVars);
                            this.sfb.unary(toTagVars);
                            if (Config.LOG_ENCODING) {
                                Logger.writeDebug("Unary: " + Arrays.toString(fromTagVars));
                                Logger.writeDebug("Unary: " + Arrays.toString(toTagVars));
                            }
                        }

                        // encode tags according to Config.TAGS_ENCODING: unary or binary
                        if (Config.NUMBERS_ENCODING.equals(Constants.UnaryBinary.UNARY)) {
                            this.sfb.iffUnaryGT(relationGTVar, fromTagVars, toTagVars);
                        } else if (Config.NUMBERS_ENCODING.equals(Constants.UnaryBinary.BINARY)) {
                            this.sfb.iffBinaryGT(relationGTVar, fromTagVars, toTagVars);
                        } else {
                            throw new RuntimeException("Illegal tags encoding: " + Config.NUMBERS_ENCODING + ".");
                        }
                        if (Config.LOG_ENCODING) {
                            Logger.writeDebug(relationGTVar + " <=> (" + Arrays.toString(fromTagVars) + " > "
                                + Arrays.toString(toTagVars) + ")");
                        }

                        // encode tags according to Config.TAGS_ENCODING: unary or binary
                        if (Config.NUMBERS_ENCODING.equals(Constants.UnaryBinary.UNARY)) {
                            this.sfb.iffUnaryGEQ(relationGEQVar, fromTagVars, toTagVars);
                        } else if (Config.NUMBERS_ENCODING.equals(Constants.UnaryBinary.BINARY)) {
                            this.sfb.iffBinaryGEQ(relationGEQVar, fromTagVars, toTagVars);
                        } else {
                            throw new RuntimeException("Illegal tags encoding: " + Config.NUMBERS_ENCODING + ".");
                        }

                        if (Config.LOG_ENCODING) {
                            Logger.writeDebug(relationGEQVar + " <=> (" + Arrays.toString(fromTagVars) + " > "
                                + Arrays.toString(toTagVars) + ")");
                        }
                    } else { // without tags
                        this.sfb.unit(CommonOperations.negateLiteral(relationGTVar));
                        if (Config.LOG_ENCODING) {
                            Logger.writeDebug("Unit: " + CommonOperations.negateLiteral(relationGTVar));
                        }
                        this.sfb.unit(relationGEQVar);
                        if (Config.LOG_ENCODING) {
                            Logger.writeDebug("Unit: " + relationGEQVar);
                        }
                    }
                }
            }
        }
    }

    public void allArgsRelations(final MCGraph mcGraph) {
        final ProgramPoint pointFrom = mcGraph.getPointFrom();
        final ProgramPoint pointTo = mcGraph.getPointTo();

        this.directionArgsRelations(mcGraph, pointFrom, pointTo, Constants.TOP_TO_BOTTOM);
        this.directionArgsRelations(mcGraph, pointTo, pointFrom, Constants.BOTTOM_TO_TOP);
        this.directionArgsRelations(mcGraph, pointFrom, pointFrom, Constants.TOP_TO_TOP);
        this.directionArgsRelations(mcGraph, pointTo, pointTo, Constants.BOTTOM_TO_BOTTOM);
    }

}
