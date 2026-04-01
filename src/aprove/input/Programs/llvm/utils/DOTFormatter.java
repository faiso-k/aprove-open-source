package aprove.input.Programs.llvm.utils;

import java.util.*;

import aprove.*;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.memory.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.states.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Functionality to output collections in LLVM graphs in DOT format.
 * @author cryingshadow
 * @version $Id$
 */
public final class DOTFormatter {

    /**
     * The limit for big entries in one line of DOT output.
     */
    public static final int BIG_DOT_NL_LIMIT = LLVMDebuggingFlags.DEBUG_NAMES_IN_OUTPUT ? 3 : 5;

    /**
     * The limit for small entries in one line of DOT output.
     */
    public static final int SMALL_DOT_NL_LIMIT = LLVMDebuggingFlags.DEBUG_NAMES_IN_OUTPUT ? 5 : 10;

    /**
     * This method creates a DOT representation of a given LLVMAbstractstate {@code state} using the HTML-like
     * tabular layout capabilities of the DOT format. Note that HTML-styled nodes must be used in the .dot file with
     * label=<...> instead of label="..."
     * @param state The state to be represented
     * @param predecessor The predecessor of state in the SEGraph, used to demonstrated changes between the Two states.
     * May be null if no differences should be shown or there are multiple predecessors (which makes showing changes too confusing)
     * @param nodeNumer The number of state. -1 if we should not draw a number.
     * @return A DOT-string representation of state
     *
     */
    public static String abstractLLVMStateToHTMLDOT(
        LLVMAbstractState state,
        LLVMAbstractState predecessor,
        int nodeNumer,
        String functionGraphLabel,
        Boolean isUnneded,
        Boolean isUnqiueStartOfRecursiveFnGraph
    ) {
        // Low-Level HTML-tags are done by the creator.
        DOTHTMLStringCreator creator = new DOTHTMLStringCreator();
        /* We create the overall table where everything else takes place.
         * CELLSPACING specifies the space between the cells, we don't want any (=0)
         * BORDER specifies the thickness of the outer borders of the table, 0 indicates no border
         * CELLBORDER specifies the thickness of cell borders
         */
        creator.enterTable("CELLSPACING=\"0\" BORDER=\"0\" CELLBORDER=\"1\" ");
        // Program Position, current Instruction
        creator.enterRow();
        /* special case error state */
        if (state.isErrorState()) {
            /* The createTextCell method is a shortcut which enters a new cell, appends the given text and exits the
             * cell afterwards
             * ALIGN specifies the text alignment within cells
             * SIDES specifies which borders/sides of a cell should be drawn. Can be a subset of L, R, T, B
             * This is needed here to hide the border between two cells with different text alignments to let it look
             * like one big cell.
             */
            creator.createTextCell("", "Error state");
            creator.exitRow();
            creator.exitTable();
            return creator.getDOTString();
        }
        if (state.isInconsistentState()) {
            /* The createTextCell method is a shortcut which enters a new cell, appends the given text and exits the
             * cell afterwards
             * ALIGN specifies the text alignment within cells
             * SIDES specifies which borders/sides of a cell should be drawn. Can be a subset of L, R, T, B
             * This is needed here to hide the border between two cells with different text alignments to let it look
             * like one big cell.
             */
            creator.createTextCell("", "Inconsistent state");
            creator.exitRow();
            creator.exitTable();
            return creator.getDOTString();
        }
        // Are we supposed to draw node numbers?
        if (nodeNumer != -1) {
            creator.enterCell("ALIGN=\"RIGHT\" CELLPADDING=\"0\" SIDES=\"lrt\" ");
            creator.appendTextToCell("#" + nodeNumer);
            if (functionGraphLabel != null) {
                creator.lineBreakWithinCell("ALIGN=\"RIGHT\"");
                creator.appendTextToCell("Graph: " + functionGraphLabel);
            }
            if (isUnneded != null && isUnneded) {
                creator.lineBreakWithinCell("ALIGN=\"RIGHT\"");
                creator.appendTextToCell("unneded Node");
            }
            if (isUnqiueStartOfRecursiveFnGraph != null && isUnqiueStartOfRecursiveFnGraph) {
                creator.lineBreakWithinCell("ALIGN=\"RIGHT\"");
                creator.appendTextToCell("recursive entry point");
            }
            creator.exitCell();
            creator.exitRow();
            creator.enterRow();
        }
        String topCellSides = nodeNumer == -1 ? "lrbt" : "lrb";
        creator.enterCell("SIDES=\"" + topCellSides + "\" ");
        if (state.isRefined()) {
            creator.appendTextToCell("pos: " + state.getProgramPosition() + " (refined)");

        } else {
            creator.appendTextToCell("pos: " + state.getProgramPosition());
        }
        // This methods evokes a line break within a text cell.
        // Note that simply adding \\n to the cell's text doesn't work!
        creator.lineBreakWithinCell();
        creator.appendTextToCell(state.getCurrentInstruction().toDOTString());
        creator.exitCell();
        creator.exitRow();
        final InformationChangeDecorator decorator = new InformationChangeDecorator() {

            @Override
            public String decorateNewElement(String inputString) {
                return "<FONT COLOR=\"darkgreen\"><B>" + inputString + "</B></FONT>";
            }

            @Override
            public String decorateRemovedElement(String inputString) {
                return "";
            }

        };
        final Comparator<String> nameComp = new LLVMNameComparator();
        final Comparator<Variable> refComp = new LLVMVariableComparator(nameComp);
        Comparator<IntegerRelation> relComp = new LLVMRelationComparator(refComp);
        final Comparator<Integer> intComp = new Comparator<Integer>() {

            @Override
            public int compare(Integer o1, Integer o2) {
                return o1.compareTo(o2);
            }

        };
        // Variables
        creator.enterRow();
        creator.enterCell("ALIGN=\"CENTER\"");
        creator.appendTextToCell("<B>Variables:</B>");
        creator.lineBreakWithinCell();
        ImmutableMap<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> previousVariables =
            predecessor == null ? null : predecessor.getProgramVariables();
        creator.appendTextToCell(
            DOTFormatter.toDOT(
                state.getProgramVariables(),
                "=",
                DOTFormatter.BIG_DOT_NL_LIMIT,
                nameComp,
                previousVariables,
                decorator,
                true,
                "<BR/>"
            )
        );
        creator.exitCell();
        creator.exitRow();
        // Allocations:
        creator.enterRow();
        creator.enterCell("ALIGN=\"CENTER\"");
        creator.appendTextToCell("<B>Allocations:</B>");
        creator.lineBreakWithinCell();
        Collection<LLVMAllocation> previousAllocations =
            predecessor == null ? null : predecessor.getAllocations();
        creator.appendTextToCell(
            DOTFormatter.toDOT(
                state.getAllocations(),
                DOTFormatter.SMALL_DOT_NL_LIMIT,
                new LLVMSimpleTermPairComparator(nameComp),
                previousAllocations,
                decorator,
                true,
                "<BR/>"
            )
        );
        creator.exitCell();
        creator.exitRow();
        // Heap:
        creator.enterRow();
        creator.enterCell("ALIGN=\"CENTER\"");
        creator.appendTextToCell("<B>Heap:</B>");
        creator.lineBreakWithinCell();
        ImmutableMap<LLVMMemoryRange, LLVMMemoryInvariant> previousHeap = predecessor == null ? null : predecessor.getMemory();
        creator.appendTextToCell(
            DOTFormatter.toDOT(
                state.getMemory(),
                "->",
                DOTFormatter.BIG_DOT_NL_LIMIT,
                new Comparator<LLVMMemoryRange>() {

                    @Override
                    public int compare(LLVMMemoryRange o1, LLVMMemoryRange o2) {
                        return nameComp.compare(o1.toString(), o2.toString());
                    }

                },
                previousHeap,
                decorator,
                true,
                "<BR/>"
            )
        );
        creator.exitCell();
        creator.exitRow();
        // Integer state:
        creator.enterRow();
        creator.enterCell("ALIGN=\"CENTER\"");
        creator.appendTextToCell("<B>Knowledge:</B>");
        creator.lineBreakWithinCell();
        creator.appendTextToCell(state.getIntegerState().toDOTString());
        creator.exitCell();
        creator.exitRow();
//        // Values:
//        creator.enterRow();
//        creator.enterCell("ALIGN=\"CENTER\"");
//        creator.appendTextToCell("<B>Values:</B>");
//        creator.lineBreakWithinCell();
//        ImmutableMap<LLVMHeuristicVariable, LLVMValue> previousValues = predecessor == null ? null : predecessor.getValues();
//        creator.appendTextToCell(
//            DOTFormatter.toDOT(
//                state.getValues(),
//                "=",
//                DOTFormatter.BIG_DOT_NL_LIMIT,
//                refComp,
//                previousValues,
//                decorator,
//                true,
//                "<BR/>"
//            )
//        );
//        creator.exitCell();
//        creator.exitRow();
//        // Associations:
//        creator.enterRow();
//        creator.enterCell("ALIGN=\"CENTER\"");
//        creator.appendTextToCell("<B>Associations:</B>");
//        creator.lineBreakWithinCell();
//        ImmutableMap<LLVMHeuristicVariable, Integer> previousAssociations =
//            predecessor == null ? null : predecessor.getAssociations();
//        ImmutableMap<LLVMHeuristicVariable, BigInteger> previousAssociationOffsets =
//            predecessor == null ? null : predecessor.getAssociationOffsets();
//        ImmutableList<ImmutablePair<LLVMHeuristicVariable, LLVMHeuristicVariable>> previousAllocations2 =
//            predecessor == null ? null : predecessor.getAllocations();
//        creator.appendTextToCell(
//            DOTFormatter.<LLVMHeuristicVariable, BigInteger>toDOT(
//                state.getAssociations(),
//                state.getAssociationOffsets(),
//                state.getAllocations(),
//                "in",
//                DOTFormatter.BIG_DOT_NL_LIMIT,
//                refComp,
//                previousAssociations,
//                previousAssociationOffsets,
//                previousAllocations2,
//                decorator,
//                true,
//                "<BR/>"
//            )
//        );
//        creator.exitCell();
//        creator.exitRow();
//        // Relations (4 sub-tables ahead):
//        IntegerRelationSet rels = new IntegerRelationSet(state.getRelations());
//        IntegerRelationSet previousRels =
//            predecessor == null ? null : new IntegerRelationSet(predecessor.getRelations());
//        creator.enterRow();
//        creator.createTextCell("SIDES=\"ltr\"  ", "<B> Relations: </B>");
//        creator.exitRow();
//        creator.enterRow();
//        creator.enterCell("SIDES=\"lbr\"");
//        creator.enterTable("CELLSPACING=\"0\" BORDER=\"0\" CELLBORDER=\"1\"");
//        creator.enterRow();
//        creator.enterCell("ALIGN=\"CENTER\"");
//        creator.appendTextToCell("<B>Inequalities:</B>");
//        creator.lineBreakWithinCell();
//        Set<LLVMRelation> previousUndirectedInequalities =
//            predecessor == null ? null : previousRels.getUndirectedInequalities();
//        creator.appendTextToCell(
//            DOTFormatter.toDOT(
//                rels.getUndirectedInequalities(),
//                DOTFormatter.BIG_DOT_NL_LIMIT,
//                relComp,
//                previousUndirectedInequalities,
//                decorator,
//                true,
//                "<BR/>"
//            )
//        );
//        creator.exitCell();
//        creator.exitRow();
//        creator.enterRow();
//        creator.enterCell("ALIGN=\"CENTER\"");
//        creator.appendTextToCell("<B>Equations:</B>");
//        creator.lineBreakWithinCell();
//        Set<LLVMRelation> previousEquations = predecessor == null ? null : previousRels.getEquations();
//        creator.appendTextToCell(
//            DOTFormatter.toDOT(
//                rels.getEquations(),
//                DOTFormatter.BIG_DOT_NL_LIMIT,
//                relComp,
//                previousEquations,
//                decorator,
//                true,
//                "<BR/>"
//            )
//        );
//        creator.exitCell();
//        creator.exitRow();
//        creator.enterRow();
//        creator.enterCell("ALIGN=\"CENTER\"");
//        creator.appendTextToCell("<B>Weak Directed Inequalities:</B>");
//        creator.lineBreakWithinCell();
//        Set<LLVMRelation> previousWeakInequalities =
//            predecessor == null ? null : previousRels.getWeakDirectedInequalities();
//        creator.appendTextToCell(
//            DOTFormatter.toDOT(
//                rels.getWeakDirectedInequalities(),
//                DOTFormatter.BIG_DOT_NL_LIMIT,
//                relComp,
//                previousWeakInequalities,
//                decorator,
//                true,
//                "<BR/>"
//            )
//        );
//        creator.exitCell();
//        creator.exitRow();
//        creator.enterRow();
//        creator.enterCell("ALIGN=\"CENTER\"");
//        creator.appendTextToCell("<B>Strict Directed Inequalities:</B>");
//        creator.lineBreakWithinCell();
//        Set<LLVMRelation> previousStrictInequalities =
//            predecessor == null ? null : previousRels.getStrictDirectedInequalities();
//        creator.appendTextToCell(
//            DOTFormatter.toDOT(
//                rels.getStrictDirectedInequalities(),
//                DOTFormatter.BIG_DOT_NL_LIMIT,
//                relComp,
//                previousStrictInequalities,
//                decorator,
//                true,
//                "<BR/>"
//            )
//        );
//        creator.exitCell();
//        creator.exitRow();
//        creator.exitTable();
//        creator.exitCell();
//        creator.exitRow();
        // Call Stack:
        creator.enterRow();
        if (state.getCallStack().isEmpty()) {
            creator.createTextCell("", "<B>Call Stack</B>: empty");
            creator.exitRow();
        } else {
            creator.createTextCell("SIDES=\"ltr\"", "<B>Call Stack</B>:");
            creator.exitRow();
            creator.enterRow();
            creator.enterCell("SIDES=\"lbr\"");
            creator.enterTable("BORDER=\"0\" CELLBORDER=\"0\"");
            // Basic idea for intended call stack elements: create a bunch of cells (~15) and "merge" them to larger
            // cells as needed.
            // Ugly hack, but DOT does not provide a mechanism for specifying widths explicitly.
            int numberofRows = state.getCallStack().size() + 15;
            int rowsProgramPos = 1 + state.getCallStack().size();
            // Create a row of invisible "fake" cells, so dot knows how many cells should be there overall.
            creator.enterRow();
            for (int i = 0; i < numberofRows; i++) {
                creator.createTextCell("", "");
            }
            creator.exitRow();
            // Actual cells each for Stack entry:
            int currentStackPos = 0;
            for (LLVMReturnInformation currentStackElement : state.getCallStack()) {
                // Should this stack entry be highlighted?
                boolean newStackEntry =
                    predecessor != null && !predecessor.getCallStack().contains(currentStackElement);
                String bgcolorAttribute = newStackEntry ? " BGCOLOR=\"green\" " : "";
                creator.enterRow();
                if (currentStackPos > 0) {
                    creator.createTextCell(bgcolorAttribute + "COLSPAN=\"" + currentStackPos + "\"", "");
                }
                creator.createTextCell(
                    bgcolorAttribute + "COLSPAN=\"" + (rowsProgramPos - currentStackPos) + "\" BORDER=\"1\" ",
                    DOTHTMLStringCreator.escapeHTMLCharacters(currentStackElement.getProgPos().toString())
                );
                int rowsRemaining = numberofRows - rowsProgramPos;
                creator.enterCell(bgcolorAttribute + "BORDER=\"1\" ALIGN=\"LEFT\" COLSPAN=\"" + rowsRemaining + "\"");
                creator.appendTextToCell(
                    "<B> Variables: </B>"
                    + DOTHTMLStringCreator.escapeHTMLCharacters(
                        DOTFormatter.toDOT(
                            currentStackElement.getProgramVariables(),
                            "=",
                            DOTFormatter.BIG_DOT_NL_LIMIT,
                            nameComp
                        )
                    )
                );
                if (!currentStackElement.getAllocationsInFunction().isEmpty()) {
                    creator.lineBreakWithinCell();
                    creator.appendTextToCell(
                        "<B> Allocated there: </B>"
                        + DOTFormatter.toDOT(
                            currentStackElement.getAllocationsInFunction(),
                            DOTFormatter.BIG_DOT_NL_LIMIT,
                            intComp,
                            null,
                            null,
                            true,
                            "<BR/>"
                        )
                    );
                }
                // Collection<A> collection, int nlLimit, Comparator<A> comparator,
                // Collection<A> previousCollection, InformationChangeDecorator decorator, boolean escapeCharactersForHTML, String newlineIndicator) {
                creator.exitCell();
                creator.exitRow();
                currentStackPos++;
            }
            creator.exitTable();
            creator.exitCell();
            creator.exitRow();
        }
        creator.exitTable();
        return creator.getDOTString();
    }

    /**
     * @param collection A collection whose items are to be formatted for DOT output.
     * @param nlLimit Insert a newline after this number of items.
     * @param comparator Comparator to sort the collection.
     * @return A DOT String containing all items of the specified set.
     */
    public static <A>String toDOT(Collection<A> collection, int nlLimit, Comparator<A> comparator) {
        return DOTFormatter.toDOT(collection, nlLimit, comparator, null, null, false, "\\n");
    }

    /**
     * @param collection A collection whose items are to be formatted for DOT output.
     * @param nlLimit Insert a newline after this number of items.
     * @param comparator Comparator to sort the collection.
     * @parm previousCollection Reference to collection of the parent state, or null if no differences should be highlighted
     * @parm decorator Does the highlighting of changes by manipulating corresponding strings
     * @parm escapeCharactersForHTML Should the result be escaped (for HTML) before returning?
     * @param newlineIndicator The string which separates lines from each other, e.g. \\n oder <BR/>
     * @return A DOT String containing all items of the specified set.
     */
    public static <A> String toDOT(
        Collection<? extends A> collection,
        int nlLimit,
        Comparator<A> comparator,
        Collection<? extends A> previousCollection,
        InformationChangeDecorator decorator,
        boolean escapeCharactersForHTML,
        String newlineIndicator
    ) {
        StringBuilder strBuilder = new StringBuilder();
        strBuilder.append("{");
        int number = 0;
        List<A> sortedList = new ArrayList<A>(collection);
        Collections.sort(sortedList, comparator);
        for (Object item : sortedList) {
            if (number > 0) {
                strBuilder.append(",");
                if (number == nlLimit) {
                    number = 0;
                    strBuilder.append(newlineIndicator);
                } else {
                    strBuilder.append(" ");
                }
            }
            number++;
            String s;
            if (item instanceof DOTStringAble) {
                s = ((DOTStringAble)item).toDOTString();
            } else {
                s = item.toString().replace('"', ' ');
            }
            if (escapeCharactersForHTML) {
                s = DOTHTMLStringCreator.escapeHTMLCharacters(s);
            }
            if (previousCollection != null) {
                if (!previousCollection.contains(item)) {
                    s = decorator.decorateNewElement(s);
                }
            }
            strBuilder.append(s);
        }
        strBuilder.append("}");
        return strBuilder.toString();
    }

    /**
     * @param map A map whose entries are to be formatted for DOT output.
     * @param connector The String between a key and value entry.
     * @param nlLimit Insert a newline after this number of entries.
     * @param comparator Comparator to sort the entries.
     * @return A DOT String containing all entries of the specified map.
     */
    public static <A>String toDOT(Map<A, ?> map, String connector, int nlLimit, Comparator<A> comparator) {
        //Backward compatibility: Don't highlight differences, don't escape for HTML, use classic new line symbol
        return DOTFormatter.toDOT(map, connector, nlLimit, comparator, null, null, false, "\\n");
    }

    /**
     * @param map A map whose entries are to be formatted for DOT output.
     * @param connector The String between a key and value entry.
     * @param nlLimit Insert a newline after this number of entries.
     * @param comparator Comparator to sort the entries.
     * @parm previousMap Reference to map of the parent state, or null if no differences should be highlighted
     * @parm decorator Does the highlighting of changes by manipulating corresponding strings
     * @parm escapeCharactersForHTML Should the result be escaped (for HTML) before returning?
     * @param newlineIndicator The string which separates lines from each other, e.g. \\n oder <BR/>
     * @return A DOT String containing all entries of the specified map.
     */
    public static <A>String toDOT(
        Map<A, ?> map,
        String connector,
        int nlLimit,
        Comparator<A> comparator,
        Map<A, ?> previousMap,
        InformationChangeDecorator decorator,
        boolean escapeCharactersForHTML,
        String newlineIndicator
    ) {
        StringBuilder strBuilder = new StringBuilder();
        strBuilder.append("{");
        int number = 0;
        List<A> sortedKeys = new ArrayList<A>(map.keySet());
        Collections.sort(sortedKeys, comparator);
        for (A key : sortedKeys) {
            number = DOTFormatter.separate(strBuilder, number, nlLimit, newlineIndicator);

            StringBuilder tempBuilder = new StringBuilder();

            DOTFormatter.appendDOT(tempBuilder, key, connector, map.get(key), escapeCharactersForHTML);

            String nextElementString = tempBuilder.toString();
            if (previousMap != null && (!previousMap.containsKey(key) || !map.get(key).equals(previousMap.get(key)))) {
                nextElementString = decorator.decorateNewElement(nextElementString);
            }

            strBuilder.append(nextElementString);
        }
        strBuilder.append("}");
        return strBuilder.toString();
    }

    /**
     * @param map1 A map whose entries are to be formatted for DOT output, but where the mapping is an index for a list
     *             and a second map provides additional information for the entries in this map.
     * @param map2 Additional information for entries in the first map.
     * @param list A list containing the mapped to objects.
     * @param connector The String between a key and value entry.
     * @param nlLimit Insert a newline after this number of entries.
     * @param comparator Comparator to sort the entries.
     * @return A DOT String containing all entries of the specified map.
     */
    public static <A, B>String toDOT(
        Map<A, Integer> map1,
        Map<A, B> map2,
        List<?> list,
        String connector,
        int nlLimit,
        Comparator<A> comparator
    ) {
        //Backward compatibility: Don't highlight differences, don't escape for HTML, use classic new line symbol
        return
            DOTFormatter.toDOT(
                map1,
                map2,
                list,
                connector,
                nlLimit,
                comparator,
                null,
                null,
                null,
                null,
                false,
                "\\n"
            );
    }

    /**
    * @param map1 A map whose entries are to be formatted for DOT output, but where the mapping is an index for a list
    *             and a second map provides additional information for the entries in this map.
    * @param map2 Additional information for entries in the first map.
    * @param list A list containing the mapped to objects.
    * @param connector The String between a key and value entry.
    * @param nlLimit Insert a newline after this number of entries.
    * @param comparator Comparator to sort the entries.
    * @parm previousMap1 Reference to map1 of the parent state, or null if no differences should be highlighted
    * @parm previousMap2 Reference to map2 of the parent state, or null if no differences should be highlighted
    * @parm previousList Reference to list of the parent state, or null if no differences should be highlighted
    * @parm decorator Does the highlighting of changes by manipulating corresponding strings
    * @parm escapeCharactersForHTML Should the result be escaped (for HTML) before returning?
    * @param newlineIndicator The string which separates lines from each other, e.g. \\n oder <BR/>
    * @return A DOT String containing all entries of the specified map.
    */
    public static <A, B>String toDOT(
        Map<A, Integer> map1,
        Map<A, B> map2,
        List<?> list,
        String connector,
        int nlLimit,
        Comparator<A> comparator,
        Map<A, Integer> previousMap1,
        Map<A, B> previousMap2,
        List<?> previousList,
        InformationChangeDecorator decorator,
        boolean escapeCharactersForHTML,
        String newlineIndicator
    ) {
        StringBuilder strBuilder = new StringBuilder();
        strBuilder.append("{");
        int number = 0;
        List<A> sortedKeys = new ArrayList<A>(map1.keySet());
        Collections.sort(sortedKeys, comparator);
        for (A key : sortedKeys) {
            number = DOTFormatter.separate(strBuilder, number, nlLimit, newlineIndicator);

            StringBuilder tempBuilder = new StringBuilder();

            DOTFormatter.appendDOT(
                tempBuilder,
                new Pair<A, B>(key, map2.get(key)),
                connector,
                list.get(map1.get(key)),
                escapeCharactersForHTML
            );

            String nextElementString = tempBuilder.toString();
            //Tests if there are changes between this map(s) and the previous one
            if (
                previousMap1 != null
                && previousMap2 != null
                && previousList != null
                && (
                    !previousMap1.containsKey(key)
                    || !previousMap2.containsKey(key)
                    || !previousMap1.get(key).equals(map1.get(key))
                    || !previousMap2.get(key).equals(map2.get(key))
                    || !previousList.get(map1.get(key)).equals(list.get(map1.get(key)))
                )
            ) {
                nextElementString = decorator.decorateNewElement(nextElementString);
            }
            strBuilder.append(nextElementString);
        }
        strBuilder.append("}");
        return strBuilder.toString();
    }

    /**
     * Converts an object to a String representation in DOT format. If the object implements the interface
     * DOTStringAble, the corresponding DOT String is returned. Otherwise its toString Method is called and the result
     * is returned without any " characters.
     * @param o The object to output in DOT format.
     * @parm escapeCharactersForHTML Should the result be escaped (for HTML) before returning?
     * @return A String containing the DOT representation of the specified object.
     */
    public static String toDOT(Object o, boolean escapeCharactersForHTML) {
        String s;
        if (o instanceof DOTStringAble) {
            s = ((DOTStringAble)o).toDOTString();
        } else {
            s = o.toString().replace('"', ' ');
        }
        if (escapeCharactersForHTML) {
            s = DOTHTMLStringCreator.escapeHTMLCharacters(s);
        }
        return s;
    }

    /**
     * Appends the following Strings to strBuilder:
     * the DOT representation of o1,
     * a whitespace character,
     * the connector,
     * a whitespace character,
     * and the DOT representation of o2.
     * @param strBuilder The StringBuilder.
     * @param o1 The first object.
     * @param connector The connector String.
     * @param o2 The second object.
     * @param escapeCharactersForHTML Should everything be escaped before appending to the StringBuilder?
     */
    private static void appendDOT(
        StringBuilder strBuilder,
        Object o1,
        String connector,
        Object o2,
        boolean escapeCharactersForHTML) {
        strBuilder.append(DOTFormatter.toDOT(o1, escapeCharactersForHTML));
        strBuilder.append(' ');
        if (escapeCharactersForHTML) {
            strBuilder.append(DOTHTMLStringCreator.escapeHTMLCharacters(connector));
        } else {
            strBuilder.append(connector);
        }
        strBuilder.append(' ');
        strBuilder.append(DOTFormatter.toDOT(o2, escapeCharactersForHTML));
    }

    /**
     * Appends a comma to the StringBuilder if the number is positive. If the number reached the nlLimit, it
     * additionally appends a newline character (in DOT format) and returns zero. Otherwise it additionally appends a
     * whitespace character and returns the specified number increased by one.
     * @param strBuilder A StringBuilder.
     * @param number A number.
     * @param nlLimit The limit for the number until a newline is inserted.
     * @param newlineIndicator The string which separates lines from each other, e.g. \\n oder <BR/>
     * @return The new number.
     */
    private static int separate(StringBuilder strBuilder, int number, int nlLimit, String newlineIndicator) {
        int res = number + 1;
        if (number > 0) {
            strBuilder.append(",");
            if (number == nlLimit) {
                res = 1;
                strBuilder.append(newlineIndicator);
            } else {
                strBuilder.append(" ");
            }
        }
        return res;
    }

    /**
     * Hides default constructor.
     */
    private DOTFormatter() {
        throw new UnsupportedOperationException("Do not instantiate me!");
    }

    /**
     * This class creates the low-level HTML-tags for nodes in a DOT-file using the tabular HTML-layout.
     * The format is documented at http://www.graphviz.org/content/node-shapes.
     * Basic idea: We use HTML tags to describe a table:
     * We have a single <TABLE> at root label, which contains rows (<TR>), which contain cells (<TD>).
     * Cells may contain text or nested tables. Extra attributes of tables and cells can be provided as a
     * space-separated list of ATTRIBUTENAME="value" elements, where the " " are mandatory for all values.
     * Enable assertions to let the Creator behave like a state machine which checks that you're not messing things up.
     * Keep in mind that special symbols (like < > ) must be escaped when being written to cells. This is not done
     * automatically to allow style attributes within text (like <B> </B> for bold).
     * @author Frank Emrich
     */
    public static class DOTHTMLStringCreator {

        private static final int STATE_IN_CELL = 4;
        private static final int STATE_IN_CELL_TABLE_DRAWN = 5;
        private static final int STATE_IN_CELL_TEXT_WRITTEN = 6;

        private static final int STATE_IN_ROW = 3;
        private static final int STATE_IN_TABLE = 2;
        //We could use an enum, of course, but no one will ever need this from outside.
        private static final int STATE_ROOT = 0;
        private static final int STATE_ROOT_TABLE_DRAWN = 1;
        /**
         * As we must escape several special characters to output them in HTML correctly, this is done here.
         * Additionally, \\n is translated to the actual HTML line break command <BR/>.
         * This method is NOT called automatically when appending text to cells, to allow the use of style modifiers (e.g. <B>.. </B> )
         * within cells without being (errorenously) escaped.
         * @param s A string containing special characters
         * @return A string where the special characters where escaped
         */
        private static String escapeHTMLCharacters(String s) {
            //StringBuilder/StringBuffer don't have methods for String-replacement, so we have to use Strings
            s = s.replace("&", "&amp;"); //Must be first replacement
            s = s.replace("<", "&lt;");
            s = s.replace(">", "&gt;");
            s = s.replace("\\n", "<BR/>");
            return s;
        }
        private int currentIndent;
        private Stack<Integer> currentState;

        private StringBuilder strBuilder;

        public DOTHTMLStringCreator() {
            this.currentIndent = 1;
            this.currentState = new Stack<Integer>();
            this.currentState.push(DOTHTMLStringCreator.STATE_ROOT);
            this.strBuilder = new StringBuilder();
        }

        /**
         * Appends text to a existing cell.
         * @param text The text to be added
         */
        public void appendTextToCell(String text) {
            if (Globals.useAssertions) {
                assert (
                    this.currentState.peek() == DOTHTMLStringCreator.STATE_IN_CELL
                    || this.currentState.peek() == DOTHTMLStringCreator.STATE_IN_CELL_TEXT_WRITTEN
                ) : "Text can only be written within text fields and no table must have been drawn in the table before";

            }
            this.tabulators(this.currentIndent);
            this.strBuilder.append(text + "\n");
            if (this.currentState.peek() == DOTHTMLStringCreator.STATE_IN_CELL) {
                this.currentState.pop();
                this.currentState.push(DOTHTMLStringCreator.STATE_IN_CELL_TEXT_WRITTEN);

            }
        }

        /**
         * Creates a new cell, adds the given text and exits the cell
         * @param attributes Additional style attributes, see DOT documentation for details
         * @param text The text to be added
         */
        public void createTextCell(String attributes, String text) {
            if (Globals.useAssertions) {
                assert (this.currentState.peek() == DOTHTMLStringCreator.STATE_IN_ROW) :
                    "Single text cells can only be created at row level";
            }
            this.tabulators(this.currentIndent);
            this.strBuilder.append("<TD " + attributes + ">\n");
            this.tabulators(this.currentIndent + 1);
            this.strBuilder.append(text + "\n");
            this.tabulators(this.currentIndent);
            this.strBuilder.append("</TD>\n");
        }

        /**
         * Creates a new cell and enters it. You may append text here or create a nested table.
         * @param attributes Additional style attributes, see DOT documentation for details
         */
        public void enterCell(String attributes) {
            if (Globals.useAssertions) {
                assert (this.currentState.peek() == DOTHTMLStringCreator.STATE_IN_ROW) :
                    "You must be at row level to enter a new cell";
            }
            this.tabulators(this.currentIndent++);
            this.strBuilder.append("<TD " + attributes + ">\n");
            this.currentState.push(DOTHTMLStringCreator.STATE_IN_CELL);
        }

        /**
         * Creates a new row within a table and enters it
         * @param attributes Additional style attributes, see DOT documentation for details
         */
        public void enterRow() {
            if (Globals.useAssertions) {
                assert (this.currentState.peek() == DOTHTMLStringCreator.STATE_IN_TABLE) :
                    "New rows can only be entered at table level";
            }
            this.tabulators(this.currentIndent++);
            this.strBuilder.append("<TR>\n");
            this.currentState.push(DOTHTMLStringCreator.STATE_IN_ROW);
        }

        /**
         * Creates a new table and enters it
         * @param attributes Additional style attributes, see DOT documentation for details
         */
        public void enterTable(String attributes) {
            if (Globals.useAssertions) {
                assert (
                    this.currentState.peek() == DOTHTMLStringCreator.STATE_ROOT
                    || this.currentState.peek() == DOTHTMLStringCreator.STATE_IN_CELL
                ) : "Must only create one table on root level or within empty cells";

            }
            this.tabulators(this.currentIndent++);
            this.strBuilder.append("<TABLE " + attributes + ">\n");
            this.currentState.push(DOTHTMLStringCreator.STATE_IN_TABLE);
        }

        /**
         * Exits the current cell and returns to row level
         */
        public void exitCell() {
            if (Globals.useAssertions) {
                assert (
                    this.currentState.peek() == DOTHTMLStringCreator.STATE_IN_CELL
                    || this.currentState.peek() == DOTHTMLStringCreator.STATE_IN_CELL_TEXT_WRITTEN
                    || this.currentState.peek() == DOTHTMLStringCreator.STATE_IN_CELL_TABLE_DRAWN
                ) : "You must be in a cell to leave one";
            }
            this.tabulators(--this.currentIndent);
            this.strBuilder.append("</TD>\n");
            this.currentState.pop();
        }

        /**
         * Exits the current row and returns to table level
         */
        public void exitRow() {
            if (Globals.useAssertions) {
                assert (this.currentState.peek() == DOTHTMLStringCreator.STATE_IN_ROW) :
                    "You must be at row level to leave one.";
            }
            this.tabulators(--this.currentIndent);
            this.strBuilder.append("</TR>\n");
            this.currentState.pop();

        }

        /**
         * Exits the table we are currently in
         */
        public void exitTable() {
            if (Globals.useAssertions) {
                assert (this.currentState.peek() == DOTHTMLStringCreator.STATE_IN_TABLE) :
                    "You must be at table level to leave one.";
            }
            this.tabulators(--this.currentIndent);
            this.strBuilder.append("</TABLE>\n");
            this.currentState.pop();
            if (this.currentState.peek() == DOTHTMLStringCreator.STATE_IN_CELL) {
                //We just left a table that was created within a cell.
                //Mark the cell as "dirty", i.e. no text must be added now.
                this.currentState.pop();
                this.currentState.push(DOTHTMLStringCreator.STATE_IN_CELL_TABLE_DRAWN);
            }
            if (this.currentState.peek() == DOTHTMLStringCreator.STATE_ROOT) {
                //Same for root level. We must not create multiple tables at root level.
                this.currentState.pop();
                this.currentState.push(DOTHTMLStringCreator.STATE_ROOT_TABLE_DRAWN);
            }

        }

        /**
         *
         * @return The string representation we created
         */
        public String getDOTString() {
            return this.strBuilder.toString();
        }

        /**
         * Creates a new line within a text cell
         */
        public void lineBreakWithinCell() {
            this.lineBreakWithinCell("");
        }

        /**
         * Creates a new line within a text cell, uses given alignment
         */
        public void lineBreakWithinCell(String alignAttribute) {
            if (Globals.useAssertions) {
                assert (
                    this.currentState.peek() == DOTHTMLStringCreator.STATE_IN_CELL
                    || this.currentState.peek() == DOTHTMLStringCreator.STATE_IN_CELL_TEXT_WRITTEN
                ) : "Line breaks only allowed within text cells";
            }
            this.tabulators(this.currentIndent);
            this.strBuilder.append("<BR " + alignAttribute + " />\n");
            if (this.currentState.peek() == DOTHTMLStringCreator.STATE_IN_CELL) {
                this.currentState.pop();
                this.currentState.push(DOTHTMLStringCreator.STATE_IN_CELL_TEXT_WRITTEN);
            }
        }

        /**
         * Little helper which adds n tabs to the output. Used to have indentation in the output to make debug easier.
         * @param n
         */
        private void tabulators(int n) {
            for (int i = 0; i < n; i++) {
                this.strBuilder.append("\t");
            }
        }

    }

    /**
     * The manipulation of DOT Strings of changed elements in collections,maps,.. is done by an InformationChangeDecorator
     * TODO: Since we currently only support highlighting newly added elements, using an interface isn't really necessary yet. Maybe remove later?
     * @author Frank
     *
     */
    public interface InformationChangeDecorator {

        /**
         * @param inputString The textual representation of a new Element (e.g. in a Collection) as compared to the previous state
         * @return A modified representation, e.g. by changing font
         */
        public String decorateNewElement(String inputString);

        /**
         * @param inputString The textual representation of a removed Element (e.g. in a Collection) as compared to the previous state
         * @return A modified representation, e.g. by changing font
         */
        public String decorateRemovedElement(String inputString);
    }

}
