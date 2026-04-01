/**
 *
 */
package aprove.input.Programs.Strategy;

import java.io.*;
import java.util.*;
import java.util.Map.Entry;

import immutables.*;

public class Parameters implements PrettyPrintable , VisitableStrategyElement {
    final ImmutableMap<String, Value> params;

    public final static Parameters EMPTY = new Parameters();

    private Parameters() {
        this(Collections.<String, Value> emptyMap());
    }

    public Parameters(Map<String, Value> map) {
        this.params = ImmutableCreator.create(map);
    }

    @Override
    public int getOneLineSize(int precedence) {
        if (this.params.isEmpty()) {
            return 0;
        }
        int n = 2 + 3 * this.params.size() + 2 + 2*(this.params.size() - 1);
        for (Entry<String, Value> e : this.params.entrySet()) {
            String key = e.getKey();
            Value value = e.getValue();
            n += key.length() + value.getOneLineSize(0);
        }
        return n;
    }
    @Override
    public void print(Appendable ap, PrettyPrintState pps) throws IOException {
        if (this.params.isEmpty()) {
            return;
        }
        boolean seperate =
            pps.getPosInLine() + this.getOneLineSize(pps.getPrecedence()) > pps.getMaxWidth();
        boolean seperateHere = seperate && this.params.size() > 1;
        int startline = pps.getLine();
        int oldindent = pps.getIndention();
        pps.append(ap, "[");
        pps.setIndention(pps.getPosInLine() - 1);
        boolean first = true;
        for (Entry<String, Value> e : this.params.entrySet()) {
            if (!first) {
                if (seperateHere) {
                    pps.newLine(ap);
                    pps.indent(ap);
                    pps.append(ap, ",");
                } else {
                    pps.append(ap, ", ");
                }
            } else {
                first = false;
            }
            String key = e.getKey();
            Value value = e.getValue();
            pps.append(ap, key);
            pps.append(ap, " = ");

            value.print(ap, pps);
        }
        if (seperate && pps.getLine() != startline) {
            pps.newLine(ap);
            pps.indent(ap);
        }
        pps.append(ap, "]");
        pps.setIndention(oldindent);
    }

    /**
     * This parameter set, as a flat, one-looong-line string
     */
    @Override
    public String toString() {
        StringBuilder builder = new StringBuilder();
        this.toBuilder(builder);
        return builder.toString();
    }

    public void toBuilder(StringBuilder target) {
        target.append("[");
        for(Map.Entry<String, Value> e: this.params.entrySet()) {
            target.append(e.getKey());
            target.append(" = ");
            e.getValue().toBuilder(target);
            target.append(", ");
        }
        if (! this.params.isEmpty()) {
            target.delete(target.length()-2, target.length());
        }
        target.append("]");
    }

    public ImmutableMap<String, Value> getMap() {
        return this.params;
    }

    @Override
    public void accept(StrategyElementVisitor visitor) {
        visitor.visit(this);
    }
}