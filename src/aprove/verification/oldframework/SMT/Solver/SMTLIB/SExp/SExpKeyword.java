package aprove.verification.oldframework.SMT.Solver.SMTLIB.SExp;

import java.util.*;

import immutables.*;

public class SExpKeyword extends SExpAtom {

    private static final ImmutableLinkedHashMap<String, SExpKeyword> keywords;
    static {
        String[] words =
            new String[] {
                ":all-statistics",
                ":authors",
                ":axioms",
                ":chainable",
                ":definition",
                ":diagnostic-output-channel",
                ":error-behavior :expand-definitions",
                ":extensions",
                ":funs",
                ":funs-description",
                ":interactive-mode",
                ":language",
                ":left-assoc",
                ":name",
                ":named",
                ":notes",
                ":print-success",
                ":produce-assignments",
                ":produce-models",
                ":produce-proofs",
                ":produce-unsat-cores",
                ":random-seed",
                ":reason-unknown",
                ":regular-output-channel",
                ":right-assoc",
                ":sorts",
                ":sorts-description",
                ":status",
                ":theories",
                ":values",
                ":verbosity",
                ":version" };
        LinkedHashMap<String, SExpKeyword> kws = new LinkedHashMap<>();
        for (String w : words) {
            kws.put(w, new SExpKeyword(w));
        }
        keywords = ImmutableCreator.create(kws);
    }

    public static SExpKeyword get(String kw) {
        return SExpKeyword.keywords.get(kw);
    }

    private final String keyword;

    private SExpKeyword(String keyword) {
        this.keyword = keyword;
    }

    @Override
    public <T> T accept(SExpVisitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        SExpKeyword other = (SExpKeyword) obj;
        if (this.keyword == null) {
            if (other.keyword != null) {
                return false;
            }
        } else if (!this.keyword.equals(other.keyword)) {
            return false;
        }
        return true;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + (this.keyword == null ? 0 : this.keyword.hashCode());
        return result;
    }

    @Override
    public String toString() {
        return this.keyword;
    }
}
