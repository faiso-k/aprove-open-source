package aprove.verification.oldframework.Utility;

import java.util.*;

import aprove.verification.oldframework.Syntax.*;

/** BitMask that will be used for filtering.
 * Setting the nth bit means filtering the nth argument. In other words:
 * - true = filter
 * - false = do not filter
 *
 * @author Christian Kaeunicke
 */
public class FilterMask extends LayeredBitSet {
    public static final int COMPARE_INCLUDES = 1;
    public static final int COMPARE_STRONGER_THAN = 2;
    public static final int COMPARE_WEAKER_THAN = 3;

    public SyntacticFunctionSymbol symbol;

    /**
     * initializes a FilterMask without a symbol.
     * You have to set a symbol later.
     */
    public FilterMask() {
        super(2);
        // will need to set symbol later
    }

    public FilterMask(final SyntacticFunctionSymbol sym) {
        super(2, sym.getArity());
        this.setSymbol(sym);
    }

    public FilterMask(final FilterMask mask) {
        this(mask.getSymbol());
        this.or(mask);
    }

    /**
     * @filter is interpreted as a boolean vector and used to initialize the FiltertMask
     * The lowest bit ist used for the first argument and a 1 becomes a filtered argument while
     * a 0 becomes a not filtered argument
     */
    public FilterMask(final SyntacticFunctionSymbol sym, int filter) {
        this(sym);

        for (int i = 0; i < sym.getArity(); i++) {
            this.set(0, i, (filter % 2 > 0));
            filter /= 2;
        }
    }

    public FilterMask copy(final boolean doDeep) {
        return new FilterMask(this);
    }

    public FilterMask applySignatureTranslation(final SignatureTranslation trans) {
        final FilterMask forReturn = new FilterMask(this);

        forReturn.symbol = trans.translate(this.symbol);
        if (forReturn.symbol == null)
         {
            forReturn.symbol = this.symbol; // keep the symbol if it's mapped to null
        }

        return forReturn;
    }

    public void setSymbol(final SyntacticFunctionSymbol sym) {
        this.symbol = sym;
    }

    public SyntacticFunctionSymbol getSymbol() {
        return this.symbol;
    }

    /**
     * @return true iff this mask filters at least very argument, that gets fitlered by the other FilterMask
     */
    public boolean strongerThan(final FilterMask other) {
        final FilterMask temp = new FilterMask(this); // copy to prevent destruction
        temp.or(other);
        return (temp.equals(this));
    }

    /**
     * @return true iff this mask filters no argument, that gets fitlered by the other FilterMask
     */
    public boolean weakerThan(final FilterMask other) {
        final FilterMask temp = new FilterMask(other); // copy to prevent destruction
        temp.or(this);
        return (temp.equals(other));
    }

    public boolean includes(final FilterMask other) {
        final BitSet myMainLayer = new BitSet();
        myMainLayer.or(this.getLayer(0)); // copy to prevent destruction
        final BitSet otherMainLayer = new BitSet();
        otherMainLayer.or(other.getLayer(0)); // copy to prevent destruction

        myMainLayer.andNot(this.getLayer(1));
        otherMainLayer.andNot(this.getLayer(1));

        return (myMainLayer.equals(otherMainLayer));
    }

    /**
     * mode can be one of:
     * - FilterMask.COMPARE_INCLUDES,
     * - FilterMask.COMPARE_STRONGER_THAN,
     * - FilterMask.COMPARE_WEAKER_THAN
     */
    public boolean compare(final FilterMask other, final int mode) {
        switch (mode) {
        case COMPARE_INCLUDES:
            return this.includes(other);
        case COMPARE_STRONGER_THAN:
            return this.strongerThan(other);
        case COMPARE_WEAKER_THAN:
            return this.weakerThan(other);
        default:
            return false;
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        final StringBuilder forReturn = new StringBuilder();
        forReturn.append(this.symbol.getName());
        forReturn.append("(");
        for (int i = 0; i < this.symbol.getArity(); i++) {
            if (i != 0) {
                forReturn.append(", ");
            }
            forReturn.append(this.get(1, i) ? "?" : (this.get(0, i) ? "a" : "g"));
        }
        forReturn.append(")");
        return forReturn.toString();
    }

    public boolean equals(final FilterMask other) {
        //obstacle course
        if (this.symbol != other.symbol) {
            return false;
        }
        if (this.symbol == null) {
            return super.equals(other);
        }
        for (int l = 0; l < this.layers; l++) {
            for (int i = 0; i < this.symbol.getArity(); i++) {
                if (this.get(l, i) != other.get(l, i)) {
                    return false;
                }
            }
        }

        // we did it
        return true;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final FilterMask other = (FilterMask) obj;
        return this.equals(other);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        int forReturn = 0;

        forReturn += this.symbol.hashCode();
        forReturn <<= 2;
        for (int l = 0; l < this.layers; l++) {
            for (int i = 0; i < this.symbol.getArity(); i++) {
                if (this.get(l, i)) {
                    forReturn += 1;
                }
            }
            forReturn <<= 2;
        }

        return forReturn;
    }

    public void changeAllAnyToQuestionMark() {
        for (int i = 0; i < this.symbol.getArity(); i++) {
            if (this.get(0, i)) {
                this.set(1, i, true);
            }
        }
    }
}
