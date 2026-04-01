package aprove.verification.dpframework.IDPProblem.utility;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 *
 * @author Martin Pluecker
 */
public class IDPExport {

    public static String exportTerm(TRSTerm t, Export_Util o, IDPPredefinedMap predefinedMap) {
        if (predefinedMap == null) {
            return t.export(o);
        } else if (t.isVariable()) {
            return t.export(o);
        } else {
            StringBuilder sb = new StringBuilder ();
            IDPExport.exportTermWithPrec(t, 0, o, new LinkedHashSet<TRSVariable>(), predefinedMap, sb);
            return sb.toString();
        }
    }

    public static String exportTerm(Collection<? extends TRSTerm> terms, Export_Util o, IDPPredefinedMap predefinedMap) {
        StringBuilder sb = new StringBuilder();
        Iterator<? extends TRSTerm> i = terms.iterator();
        while(i.hasNext()) {
            sb.append(IDPExport.exportTerm(i.next(), o, predefinedMap));
            if (i.hasNext()) {
                sb.append(o.linebreak());
            }
        }
        return sb.toString();
    }

    public static String exportRule(GeneralizedRule r, Export_Util o, IDPPredefinedMap predefinedMap) {
        TRSTerm lhs = r.getLeft();
        TRSTerm rhs = r.getRight();
        Set<TRSVariable> freeVars = rhs.getVariables();
        freeVars.removeAll(lhs.getVariables());
        StringBuilder sb = new StringBuilder();
        IDPExport.exportTermWithPrec(lhs, 0, o, freeVars, predefinedMap, sb);
        sb.append(" ");
        sb.append(o.rightarrow());
        sb.append(" ");
        IDPExport.exportTermWithPrec(rhs, 0, o, freeVars, predefinedMap, sb);
        return sb.toString();
    }

    public static String exportRule(Collection<? extends GeneralizedRule> rules, Export_Util o, IDPPredefinedMap predefinedMap) {
        StringBuilder sb = new StringBuilder();
        Iterator<? extends GeneralizedRule> i = rules.iterator();
        while(i.hasNext()) {
            sb.append(IDPExport.exportRule(i.next(), o, predefinedMap));
            if (i.hasNext()) {
                sb.append(o.linebreak());
            }
        }
        return sb.toString();
    }

    public static enum PositionMarker {
        UNDERLINE {
            @Override
            String getHTMLStart() {
                return "<u>";
            }

            @Override
            String getHTMLEnd() {
                return "</u>";
            }
        },
        BOLD {
            @Override
            String getHTMLStart() {
                return "<b>";
            }

            @Override
            String getHTMLEnd() {
                return "</b>";
            }
        },
        BOLD_UNDERLINE {
            @Override
            String getHTMLStart() {
                return "<u><b>";
            }

            @Override
            String getHTMLEnd() {
                return "</b></u>";
            }
        };
        abstract String getHTMLStart();

        abstract String getHTMLEnd();
    };

    /**
     * Writes a representation (depending on the {@link Export_Util} {@code eu})
     * of the {@link TRSTerm} {@code t} to the {@link StringBuilder} sb.
     * <p>
     * The representation will use infix notation with precedence but keep the
     * term structure recognizable. For example the term
     * <code>+(+(x, y), z)</code> will export as <code>x + y + z</code> (since
     * <code>+</code> is defined with left-to-right associativity, but
     * <code>+(x, +(y, z))</code> will export as <code>x + (y + z)</code>.
     * </p>
     * @param t The term to export.
     * @param prec The precedence of the context in which the term is written
     * to. Usually use 0 here.
     * @param eu The fine {@link Export_Util} used to render the markup.
     * @param freeVars Free variables are marked in bold, green font.
     * @param predefinedMap The predefined operators.
     * @param sb The {@link StringBuilder} on which the representation is
     * appended.
     */
    public static void exportTermWithPrec(
        final TRSTerm t,
        final int prec,
        final Export_Util eu,
        final Collection<TRSVariable> freeVars,
        final IDPPredefinedMap predefinedMap,
        final StringBuilder sb)
    {
        LinkedHashMap<Position, PositionMarker> markedPositions = new LinkedHashMap<>();
        IDPExport.exportTermWithPrec(t, prec, eu, freeVars, predefinedMap, sb, Position.EPSILON, markedPositions);
    }

    /**
     * Writes a representation (depending on the {@link Export_Util} {@code eu})
     * of the {@link TRSTerm} {@code t} to the {@link StringBuilder} sb.
     * <p>
     * The representation will use infix notation with precedence but keep the
     * term structure recognizable. For example the term
     * <code>+(+(x, y), z)</code> will export as <code>x + y + z</code> (since
     * <code>+</code> is defined with left-to-right associativity, but
     * <code>+(x, +(y, z))</code> will export as <code>x + (y + z)</code>.
     * </p>
     * @param t The term to export.
     * @param prec The precedence of the context in which the term is written
     * to. Usually use 0 here.
     * @param eu The fine {@link Export_Util} used to render the markup.
     * @param free Free variables are marked in bold, green font.
     * @param pd The predefined operators.
     * @param sb The {@link StringBuilder} on which the representation is
     * appended.
     * @param marked Map of positions that should be highlighted in some way.
     */
    public static void exportTermWithPrec(
        final TRSTerm t,
        final int prec,
        final Export_Util eu,
        final Collection<TRSVariable> free,
        final IDPPredefinedMap pd,
        final StringBuilder sb,
        final Map<Position, PositionMarker> marked)
    {
        IDPExport.exportTermWithPrec(t, prec, eu, free, pd, sb, Position.EPSILON, marked == null
            ? new LinkedHashMap<Position, PositionMarker>()
                : marked);
    }

    private static void exportTermWithPrec(
        final TRSTerm t,
        final int precedence,
        final Export_Util exportUtil,
        final Collection<TRSVariable> free,
        final IDPPredefinedMap predef,
        final StringBuilder sb,
        final Position position,
        final Map<Position, PositionMarker> marked)
    {
        PositionMarker marker = marked.get(position);
        if (marker != null && exportUtil instanceof HTML_Util) {
            sb.append(marker.getHTMLStart());
        }
        if (t.isVariable()) {
            sb.append(t.export(exportUtil, free));
        } else {
            TRSFunctionApplication fa = (TRSFunctionApplication) t;
            ImmutableList<TRSTerm> args = fa.getArguments();
            int arity = args.size();
            final FunctionSymbol f = fa.getRootSymbol();
            final Integer fPrec = predef.getInfixLTRPrecedence(f);

            if (fPrec != null) {
                // f is a predefined Left-To-Right infix operator with precedence fPrec
                if (fPrec < precedence) {
                    sb.append("(");
                }
                IDPExport.exportTermWithPrec(args.get(0), fPrec, exportUtil, free, predef, sb, position.append(0), marked);
                sb.append(" ");
                sb.append(f.export(exportUtil));
                sb.append(" ");
                IDPExport.exportTermWithPrec(args.get(1), fPrec + 1, exportUtil, free, predef, sb, position.append(0), marked);
                if (fPrec < precedence) {
                    sb.append(")");
                }
            } else {
                // otherwise, we show it as before...
                sb.append(f.export(exportUtil));
                if (arity > 0) {
                    sb.append("(");
                    for (int i = 0; i < arity; ++i) {
                        if (i != 0) {
                            sb.append(", ");
                        }
                        IDPExport.exportTermWithPrec(args.get(i), 0, exportUtil, free, predef, sb, position.append(i), marked);
                    }
                    sb.append(")");
                }
            }
        }
        if (marker != null && exportUtil instanceof HTML_Util) {
            sb.append(marker.getHTMLEnd());
        }
    }

}
