package aprove.verification.dpframework.TRSProblem.Utility.SRSNonLoop;

import java.util.*;

import org.w3c.dom.*;

import aprove.verification.oldframework.BasicStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * represents WordPattern (l,m,r,f)<br>
 * with {@link StringPattern} l,m,r <br>
 * and {@link LinearFunction} f
 */
public class WordPattern implements Immutable, CPFAdditional {

    private final StringPattern l;
    private final StringPattern m;
    private final StringPattern r;
    private final LinearFunction f;
    private final int hashCode;

    public WordPattern(StringPattern l, StringPattern m, StringPattern r,
            LinearFunction f) {
        this.l = l;
        this.m = m;
        this.r = r;
        this.f = f;
        this.hashCode = this.newHashCode();
    }

    /**
     * rotate operation <br>
     * Definition 5.1.1 page 17/18
     * @return Set of generated {@link WordPattern}
     */
    public Set<WordPattern> rotate() {
        // (l (ml mr)^(k + 1) r) -> l ml (mr ml)^k mr r)
        Set<WordPattern> rotations = new LinkedHashSet<WordPattern>();
        if (this.f.getAbs() >= 1) {
            for (int i = 1; i < this.m.size(); i++) {
                List<FunctionSymbol> newL =
                    new ArrayList<FunctionSymbol>(this.l.getList());
                newL.addAll(this.m.getSublist(0, i));
                List<FunctionSymbol> newR =
                    new ArrayList<FunctionSymbol>(this.m.getSublist(i, this.m.size()));
                newR.addAll(this.r.getList());
                List<FunctionSymbol> newM =
                    new ArrayList<FunctionSymbol>(this.m.getSublist(i, this.m.size()));
                newM.addAll(this.m.getSublist(0, i));
                LinearFunction newF =
                    new LinearFunction(this.f.getLin(), this.f.getAbs() - 1);

                rotations.add(new WordPattern(new StringPattern(newL),
                    new StringPattern(newM), new StringPattern(newR), newF));
            }
        }
        return rotations;
    }

    /**
     * expand operation <br>
     * Definition 5.1.2 page 18/19<br>
     * 2 ways to expand
     * <ul>
     * <li>w -> w' = (l m,m,r,f)</li>
     * <li>w -> w' = (l,m,m r,f)</li>
     * </ul>
     * @return Set of generated {@link WordPattern}
     */
    public Set<WordPattern> expand() {
        Set<WordPattern> expansions = new LinkedHashSet<WordPattern>();

        if (this.f.getAbs() >= 1) {

            // w -> w' = (l m,m,r,f)
            List<FunctionSymbol> newL =
                new ArrayList<FunctionSymbol>(this.l.getList());
            newL.addAll(this.m.getList());
            LinearFunction newF =
                new LinearFunction(this.f.getLin(), this.f.getAbs() - 1);

            expansions.add(new WordPattern(new StringPattern(newL),
                new StringPattern(this.m.getList()), new StringPattern(this.r.getList()),
                newF));

            // w -> w' = (l,m,m r,f)
            List<FunctionSymbol> newR =
                new ArrayList<FunctionSymbol>(this.m.getList());
            newR.addAll(this.r.getList());

            newF = new LinearFunction(this.f.getLin(), this.f.getAbs() - 1);

            expansions.add(new WordPattern(new StringPattern(this.l.getList()),
                new StringPattern(this.m.getList()), new StringPattern(newR), newF));
        }
        return expansions;
    }

    /**
     * lift operation<br>
     * Definition 5.1.3 page 19/20
     * @return Set of generated {@link WordPattern}
     */
    public WordPattern lift() {
        return new WordPattern(new StringPattern(this.l.getList()),
            new StringPattern(this.m.getList()), new StringPattern(this.r.getList()),
            new LinearFunction(this.f.getLin(), this.f.getAbs() + this.f.getLin()));
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

    public int newHashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.f == null) ? 0 : this.f.hashCode());
        result = prime * result + ((this.l == null) ? 0 : this.l.hashCode());
        result = prime * result + ((this.m == null) ? 0 : this.m.hashCode());
        result = prime * result + ((this.r == null) ? 0 : this.r.hashCode());
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (this.hashCode != obj.hashCode()) {
            return false;
        }

        if (obj instanceof WordPattern) {
            WordPattern wp = (WordPattern) obj;
            return this.l.equals(wp.getL()) && this.m.equals(wp.getM())
                && this.r.equals(wp.getR()) && this.f.equals(wp.getF());
        }
        return false;
    }

    public StringPattern getL() {
        return this.l;
    }

    public StringPattern getM() {
        return this.m;
    }

    public StringPattern getR() {
        return this.r;
    }

    public LinearFunction getF() {
        return this.f;
    }

    @Override
    public String toString() {
        return this.l + " (" + this.m + ")^" + this.f + " " + this.r;
    }

    @Override
    public Element toCPF(Document doc, XMLMetaData xmlMetaData) {
        return CPFTag.WORD_PATTERN.create(doc,
                this.l.toCPF(doc, xmlMetaData),
                this.m.toCPF(doc, xmlMetaData),
                CPFTag.FACTOR.create(doc, doc.createTextNode(this.f.getLin() + "")),
                CPFTag.CONSTANT.create(doc, doc.createTextNode(this.f.getAbs() + "")),
                this.r.toCPF(doc, xmlMetaData));
    }
}
