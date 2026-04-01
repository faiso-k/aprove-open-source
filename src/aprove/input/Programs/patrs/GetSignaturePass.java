package aprove.input.Programs.patrs;

import java.util.*;

import aprove.input.Generated.patrs.node.*;
import aprove.input.Utility.*;

/**
 * Treewalker which collects all sorted function symbols and computes the defined symbols.
 *
 * @author Stephan Falke
 * @version $Id$
 */
public class GetSignaturePass extends Pass {

    private boolean inFunDecl;
    private String currentFun;
    private List<String> currentSorts;
    private final Set<String> funs;
    private final Set<String> defs;
    private final Map<String, List<String>> sorts;
    private final Map<String, Set<Integer>> mu;
    private Set<Integer> currentInts;

    public GetSignaturePass() {
        this.inFunDecl = false;
        this.currentFun = null;
        this.currentSorts = null;
        this.currentInts = null;
        this.funs = new LinkedHashSet<String>();
        this.sorts = new LinkedHashMap<String, List<String>>();
        this.defs = new LinkedHashSet<String>();
        this.mu = new LinkedHashMap<String, Set<Integer>>();

        final List<String> si = new Vector<String>();
        si.add("int");
        final List<String> sii = new Vector<String>();
        sii.add("int");
        sii.add("int");
        final List<String> siii = new Vector<String>();
        siii.add("int");
        siii.add("int");
        siii.add("int");

        this.sorts.put("0", si);
        this.sorts.put("1", si);
        this.sorts.put("-", sii);
        this.sorts.put("+", siii);
    }

    @Override
    public void inAFdecllist(final AFdecllist node) {
        this.inFunDecl = true;
    }

    @Override
    public void outAFdecllist(final AFdecllist node) {
        this.inFunDecl = false;
    }

    @Override
    public void inAFdecl(final AFdecl node) {
        this.currentSorts = new Vector<String>();
    }

    @Override
    public void outAFdecl(final AFdecl node) {
        /*if (this.currentSorts.get(this.currentSorts.size() - 1).equals("int")) {
            this.addParseError(node.getArrow(), ParseError.ERROR, "'int' is currently not allowed as return type");
        } else {
            this.sorts.put(this.currentFun, this.currentSorts);
        }*/
        this.sorts.put(this.currentFun, this.currentSorts);
    }

    @Override
    public void inACsdecl(final ACsdecl node) {
        this.currentInts = new LinkedHashSet<Integer>();
    }

    @Override
    public void outACsdecl(final ACsdecl node) {
        this.mu.put(this.currentFun, this.currentInts);
    }

    @Override
    public void inAIntegerIntt(final AIntegerIntt node) {
        final String name = this.chop(node);
        final Integer tmp = Integer.valueOf(name);
        this.currentInts.add(Integer.valueOf(tmp.intValue() - 1));
    }

    @Override
    public void inASpecialIntt(final ASpecialIntt node) {
        final String name = this.chop(node);
        if (name.equals("+") || name.equals("-") || name.equals("0")) {
            this.addParseError(node.getSpecialid(), ParseError.ERROR, "id not allowed in replacement map");
        } else {
            this.currentInts.add(Integer.valueOf(0));
        }
    }

    @Override
    public void inAUnivSortid(final AUnivSortid node) {
        this.currentSorts.add("univ");
    }

    @Override
    public void inAIntSortid(final AIntSortid node) {
        this.currentSorts.add("int");
    }

    @Override
    public void inARegularId(final ARegularId node) {
        if (this.inFunDecl) {
            final String name = this.chop(node);
            if (this.funs.contains(name)) {
                this.addParseError(node.getRegularid(), ParseError.ERROR, "id already declared");
            } else {
                this.funs.add(name);
            }
            this.currentFun = name;
        }
    }

    @Override
    public void inASpecialId(final ASpecialId node) {
        if (this.inFunDecl) {
            this.addParseError(node.getSpecialid(), ParseError.ERROR, "integer ids cannot be redeclared");
        }
    }

    @Override
    public void inASimple(final ASimple node) {
        final PTerm p = node.getLeft();
        PId pp = null;
        Token t = null;
        if (p instanceof AConstVarTerm) {
            pp = ((AConstVarTerm) p).getId();
        } else if (p instanceof AFunctAppTerm) {
            pp = ((AFunctAppTerm) p).getId();
        }
        if (pp instanceof ARegularId) {
            t = ((ARegularId) pp).getRegularid();
        } else if (pp instanceof ASpecialId) {
            t = ((ASpecialId) pp).getSpecialid();
        } else {
            assert (false);
        }
        final String name = this.chop(t);
        if (!this.funs.contains(name)) {
            this.addParseError(t, ParseError.ERROR, "undeclared id");
        } else {
            this.defs.add(name);
        }
    }

    public Set<String> getFuns() {
        return this.funs;
    }

    public Set<String> getDefs() {
        return this.defs;
    }

    public Map<String, List<String>> getSortMap() {
        return this.sorts;
    }

    public Map<String, Set<Integer>> getMu() {
        return this.mu;
    }
}
