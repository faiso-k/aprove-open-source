package aprove.input.Programs.patrs;

import java.util.*;

import aprove.input.Generated.patrs.node.*;
import aprove.input.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Treewalker which generates E and S.
 *
 * @author Stephan Falke
 * @version $Id$
 */
public class CreateBuiltinPass extends Pass {

    private static final int LIST = -1;
    private static final int SEQ = 0;
    private static final int MSET_INS = 1;
    private static final int MSET_UNI = 2;
    private static final int SET_INS = 3;
    private static final int SET_UNI = 4;
    private static final int COMP_INS = 5;
    private static final int COMP_UNI = 6;

    private boolean inUseDecl;
    private int currentUse;
    private Token currentUseToken;
    private List<String> builtinFuns;
    private Set<String> allBuiltin;
    private Set<String> funs;
    private Map<String, List<String>> sorts;
    private Set<String> defs;
    private Set<Equation> E;
    private Set<Rule> S;

    public CreateBuiltinPass(Set<String> funs, Map<String, List<String>> sorts, Set<String> defs) {
        this.inUseDecl = false;
        this.currentUse = 2107;
        this.currentUseToken = null;
        this.funs = funs;
        this.sorts = sorts;
        this.defs = defs;
        this.E = new LinkedHashSet<Equation>();
        this.S = new LinkedHashSet<Rule>();
        this.allBuiltin = new LinkedHashSet<String>();
        this.E.addAll(this.getPAE());
        this.S.addAll(this.getPAS());
    }

    private Set<Equation> getPAE() {
        Set<Equation> res = new LinkedHashSet<Equation>();

        FreshNameGenerator fng = new FreshNameGenerator(this.funs, FreshNameGenerator.VARIABLES);
        TRSVariable x = TRSTerm.createVariable(fng.getFreshName("x", false));
        TRSVariable y = TRSTerm.createVariable(fng.getFreshName("y", false));
        TRSVariable z = TRSTerm.createVariable(fng.getFreshName("z", false));
        FunctionSymbol plus = FunctionSymbol.create("+", 2);

        res.add(this.constructA(plus, x, y, z));
        res.add(this.constructC(plus, x, y));

        return res;
    }

    private Set<Rule> getPAS() {
        Set<Rule> res = new LinkedHashSet<Rule>();

        FreshNameGenerator fng = new FreshNameGenerator(this.funs, FreshNameGenerator.VARIABLES);
        TRSVariable x = TRSTerm.createVariable(fng.getFreshName("x", false));
        TRSVariable y = TRSTerm.createVariable(fng.getFreshName("y", false));
        FunctionSymbol zero = FunctionSymbol.create("0", 0);
        FunctionSymbol minus = FunctionSymbol.create("-", 1);
        FunctionSymbol plus = FunctionSymbol.create("+", 2);

        res.add(this.constructU(plus, zero, x, false));
        res.add(this.constructMM(minus, x));
        res.add(this.constructMZ(minus, zero));
        res.add(this.constructMP(minus, plus, x, y));
        res.addAll(this.constructCancel(plus, minus, zero, x, y));

        return res;
    }

    private Rule constructMM(FunctionSymbol minus, TRSVariable x) {
        Vector<TRSTerm> args = new Vector<TRSTerm>();
        args.add(x);
        TRSFunctionApplication tmp = this.createTerm(minus, args);

        args = new Vector<TRSTerm>();
        args.add(tmp);
        TRSFunctionApplication lhs = this.createTerm(minus, args);
        return Rule.create(lhs, x);
    }

    private Rule constructMZ(FunctionSymbol minus, FunctionSymbol zero) {
        TRSFunctionApplication zerot = this.createTerm(zero, new Vector<TRSTerm>());
        Vector<TRSTerm> args = new Vector<TRSTerm>();
        args.add(zerot);
        TRSFunctionApplication lhs = this.createTerm(minus, args);
        return Rule.create(lhs, zerot);
    }

    private Rule constructMP(FunctionSymbol minus, FunctionSymbol plus, TRSVariable x, TRSVariable y) {
        Vector<TRSTerm> args = new Vector<TRSTerm>();
        args.add(x);
        args.add(y);
        TRSFunctionApplication fxy = this.createTerm(plus, args);

        args = new Vector<TRSTerm>();
        args.add(fxy);
        TRSFunctionApplication lhs = this.createTerm(minus, args);

        args = new Vector<TRSTerm>();
        args.add(x);
        TRSFunctionApplication gx = this.createTerm(minus, args);

        args = new Vector<TRSTerm>();
        args.add(y);
        TRSFunctionApplication gy = this.createTerm(minus, args);

        args = new Vector<TRSTerm>();
        args.add(gx);
        args.add(gy);
        TRSFunctionApplication rhs = this.createTerm(plus, args);

        return Rule.create(lhs, rhs);
    }

    private Set<Rule> constructCancel(FunctionSymbol plus, FunctionSymbol minus, FunctionSymbol zero, TRSVariable x, TRSVariable y) {
        Set<Rule> res = new LinkedHashSet<Rule>();
        TRSFunctionApplication zerot = this.createTerm(zero, new Vector<TRSTerm>());

        Vector<TRSTerm> args = new Vector<TRSTerm>();
        args.add(x);
        TRSFunctionApplication gx = this.createTerm(minus, args);

        args = new Vector<TRSTerm>();
        args.add(x);
        args.add(gx);
        TRSFunctionApplication lhs = this.createTerm(plus, args);
        res.add(Rule.create(lhs, zerot));

        args = new Vector<TRSTerm>();
        args.add(lhs);
        args.add(y);
        lhs = this.createTerm(plus, args);
        res.add(Rule.create(lhs, y));

        return res;
    }

    @Override
    public void inAUsedecllist(AUsedecllist node) {
        this.inUseDecl = true;
    }

    @Override
    public void outAUsedecllist(AUsedecllist node) {
        this.inUseDecl = false;
    }

    @Override
    public void inAListiBuiltinid(AListiBuiltinid node) {
        this.currentUse = CreateBuiltinPass.LIST;
        this.currentUseToken = node.getList();
    }

    @Override
    public void inASequBuiltinid(ASequBuiltinid node) {
        this.currentUse = CreateBuiltinPass.SEQ;
        this.currentUseToken = node.getSeq();
    }

    @Override
    public void inAMulsetInsBuiltinid(AMulsetInsBuiltinid node) {
        this.currentUse = CreateBuiltinPass.MSET_INS;
        this.currentUseToken = node.getMulsetins();
    }

    @Override
    public void inAMulsetUniBuiltinid(AMulsetUniBuiltinid node) {
        this.currentUse = CreateBuiltinPass.MSET_UNI;
        this.currentUseToken = node.getMulsetuni();
    }

    @Override
    public void inACompactInsBuiltinid(ACompactInsBuiltinid node) {
        this.currentUse = CreateBuiltinPass.COMP_INS;
        this.currentUseToken = node.getCompactins();
    }

    @Override
    public void inACompactUniBuiltinid(ACompactUniBuiltinid node) {
        this.currentUse = CreateBuiltinPass.COMP_UNI;
        this.currentUseToken = node.getCompactuni();
    }

    @Override
    public void inASetInsBuiltinid(ASetInsBuiltinid node) {
        this.currentUse = CreateBuiltinPass.SET_INS;
        this.currentUseToken = node.getSetins();
    }

    @Override
    public void inASetUniBuiltinid(ASetUniBuiltinid node) {
        this.currentUse = CreateBuiltinPass.SET_UNI;
        this.currentUseToken = node.getSetuni();
    }

    @Override
    public void inAIdlist(AIdlist node) {
        if (this.inUseDecl) {
            this.builtinFuns = new Vector<String>();
        }
    }

    @Override
    public void outAIdlist(AIdlist node) {
        if (this.inUseDecl) {
            switch (this.currentUse) {
            case SEQ:
            case MSET_UNI:
            case SET_UNI:
            case COMP_UNI:
                if (this.builtinFuns.size() != 3) {
                    this.addParseError(this.currentUseToken, ParseError.ERROR, "3 ids expected");
                } else {
                    if (this.check_constant() && this.check_sorts_three()) {
                        this.addPredef();
                    }
                }
                break;
            case LIST:
            case MSET_INS:
            case SET_INS:
            case COMP_INS:
                if (this.builtinFuns.size() != 2) {
                    this.addParseError(this.currentUseToken, ParseError.ERROR, "2 ids expected");
                } else {
                    if (this.check_constant() && this.check_sorts_two()) {
                        this.addPredef();
                    }
                }
                break;
            default:
                break;
            }
        }
    }

    private void addPredef() {
        FreshNameGenerator fng = new FreshNameGenerator(this.funs, FreshNameGenerator.VARIABLES);
        TRSVariable x = TRSTerm.createVariable(fng.getFreshName("x", false));
        TRSVariable y = TRSTerm.createVariable(fng.getFreshName("y", false));
        TRSVariable z = TRSTerm.createVariable(fng.getFreshName("z", false));

        FunctionSymbol constsymb = FunctionSymbol.create(this.builtinFuns.get(0), 0);
        FunctionSymbol inssymb = null;

        switch (this.currentUse) {
        case MSET_INS:
            inssymb = FunctionSymbol.create(this.builtinFuns.get(1), 2);
            this.E.add(this.constructSwap(inssymb, x, y, z));
            break;
        case SET_INS:
            inssymb = FunctionSymbol.create(this.builtinFuns.get(1), 2);
            this.E.add(this.constructSwap(inssymb, x, y, z));
            this.S.add(this.constructColl(inssymb, x, y));
            break;
        case COMP_INS:
            inssymb = FunctionSymbol.create(this.builtinFuns.get(1), 2);
            this.S.add(this.constructColl(inssymb, x, y));
            break;
        case SEQ:
            inssymb = FunctionSymbol.create(this.builtinFuns.get(2), 2);
            this.E.add(this.constructA(inssymb, x, y, z));
            this.S.add(this.constructU(inssymb, constsymb, x, false));
            this.S.add(this.constructU(inssymb, constsymb, x, true));
            break;
        case MSET_UNI:
            inssymb = FunctionSymbol.create(this.builtinFuns.get(2), 2);
            this.E.add(this.constructA(inssymb, x, y, z));
            this.E.add(this.constructC(inssymb, x, y));
            this.S.add(this.constructU(inssymb, constsymb, x, false));
            break;
        case SET_UNI:
            inssymb = FunctionSymbol.create(this.builtinFuns.get(2), 2);
            this.E.add(this.constructA(inssymb, x, y, z));
            this.E.add(this.constructC(inssymb, x, y));
            this.S.add(this.constructU(inssymb, constsymb, x, false));
            this.S.addAll(this.constructI(inssymb, x, y, true));
            break;
        case COMP_UNI:
            inssymb = FunctionSymbol.create(this.builtinFuns.get(2), 2);
            FunctionSymbol wrapper = FunctionSymbol.create(this.builtinFuns.get(1), 1);
            Vector<TRSTerm> args = new Vector<TRSTerm>();
            args.add(x);
            TRSFunctionApplication wrapx = this.createTerm(wrapper, args);
            this.E.add(this.constructA(inssymb, x, y, z));
            this.S.add(this.constructU(inssymb, constsymb, x, false));
            this.S.add(this.constructU(inssymb, constsymb, x, true));
            this.S.addAll(this.constructI(inssymb, wrapx, y, false));
            break;
        default:
            break;
        }
    }

    private TRSFunctionApplication createTerm(FunctionSymbol f, List<TRSTerm> args) {
        TRSTerm[] nargs = new TRSTerm[args.size()];
        for (int i = 0; i < args.size(); i++) {
            nargs[i] = args.get(i);
        }
        return TRSTerm.createFunctionApplication(f, nargs);
    }

    private Equation constructSwap(FunctionSymbol f, TRSVariable x, TRSVariable y, TRSVariable z) {
        Vector<TRSTerm> args = new Vector<TRSTerm>();
        args.add(y);
        args.add(z);
        TRSTerm fyz = this.createTerm(f, args);
        args = new Vector<TRSTerm>();
        args.add(x);
        args.add(fyz);
        TRSTerm fxfyz = this.createTerm(f, args);

        args = new Vector<TRSTerm>();
        args.add(x);
        args.add(z);
        TRSTerm fxz = this.createTerm(f, args);
        args = new Vector<TRSTerm>();
        args.add(y);
        args.add(fxz);
        TRSTerm fyfxz = this.createTerm(f, args);

        return Equation.create(fxfyz, fyfxz);
    }

    private Equation constructA(FunctionSymbol f, TRSVariable x, TRSVariable y, TRSVariable z) {
        Vector<TRSTerm> args = new Vector<TRSTerm>();
        args.add(y);
        args.add(z);
        TRSTerm fyz = this.createTerm(f, args);
        args = new Vector<TRSTerm>();
        args.add(x);
        args.add(fyz);
        TRSTerm fxfyz = this.createTerm(f, args);

        args = new Vector<TRSTerm>();
        args.add(x);
        args.add(y);
        TRSTerm fxy = this.createTerm(f, args);
        args = new Vector<TRSTerm>();
        args.add(fxy);
        args.add(z);
        TRSTerm ffxyz = this.createTerm(f, args);

        return Equation.create(fxfyz, ffxyz);
    }

    private Equation constructC(FunctionSymbol f, TRSVariable x, TRSVariable y) {
        Vector<TRSTerm> args = new Vector<TRSTerm>();
        args.add(x);
        args.add(y);
        TRSTerm fxy = this.createTerm(f, args);
        args = new Vector<TRSTerm>();
        args.add(y);
        args.add(x);
        TRSTerm fyx = this.createTerm(f, args);

        return Equation.create(fxy, fyx);
    }

    private Rule constructColl(FunctionSymbol f, TRSVariable x, TRSVariable y) {
        Vector<TRSTerm> args = new Vector<TRSTerm>();
        args.add(x);
        args.add(y);
        TRSTerm fxy = this.createTerm(f, args);
        args = new Vector<TRSTerm>();
        args.add(x);
        args.add(fxy);
        TRSFunctionApplication fxfxy = this.createTerm(f, args);

        return Rule.create(fxfxy, fxy);
    }

    private Rule constructU(FunctionSymbol f, FunctionSymbol unit, TRSVariable x, boolean left) {
        Vector<TRSTerm> args = new Vector<TRSTerm>();
        if (left) {
            args.add(this.createTerm(unit, new Vector<TRSTerm>()));
            args.add(x);
        } else {
            args.add(x);
            args.add(this.createTerm(unit, new Vector<TRSTerm>()));
        }
        TRSFunctionApplication lhs = this.createTerm(f, args);

        return Rule.create(lhs, x);
    }

    private Set<Rule> constructI(FunctionSymbol f, TRSTerm x, TRSVariable y, boolean extended) {
        Set<Rule> res = new LinkedHashSet<Rule>();

        Vector<TRSTerm> args = new Vector<TRSTerm>();
        args.add(x);
        args.add(x);
        TRSFunctionApplication lhs = this.createTerm(f, args);
        res.add(Rule.create(lhs, x));

        if (extended) {
            args = new Vector<TRSTerm>();
            args.add(lhs);
            args.add(y);
            lhs = this.createTerm(f, args);
            args = new Vector<TRSTerm>();
            args.add(x);
            args.add(y);
            TRSFunctionApplication rhs = this.createTerm(f, args);
            res.add(Rule.create(lhs, rhs));
        }

        return res;
    }

    private boolean check_constant() {
        String name = this.builtinFuns.get(0);
        if (this.defs.contains(name)) {
            this.addParseError(this.currentUseToken, ParseError.ERROR, "first id cannot be defined symbol");
            return false;
        }
        List<String> csorts = this.sorts.get(name);
        if (csorts == null) {
            this.addParseError(this.currentUseToken, ParseError.ERROR, "first id not declared");
            return false;
        }
        if (csorts.size() != 1 || csorts.get(0) != "univ") {
            this.addParseError(this.currentUseToken, ParseError.ERROR, "first id has incompatible sorts");
            return false;
        }
        if (this.allBuiltin.contains(name)) {
            this.addParseError(this.currentUseToken, ParseError.ERROR, "first id is used in more than one 'use' declaration");
            return false;
        }
        this.allBuiltin.add(name);
        return true;
    }

    private boolean check_sorts_three() {
        String name1 = this.builtinFuns.get(1);
        String name2 = this.builtinFuns.get(2);
        if (this.defs.contains(name1)) {
            this.addParseError(this.currentUseToken, ParseError.ERROR, "second id cannot be defined symbol");
            return false;
        }
        if (this.defs.contains(name2)) {
            this.addParseError(this.currentUseToken, ParseError.ERROR, "third id cannot be defined symbol");
            return false;
        }
        List<String> csorts1 = this.sorts.get(name1);
        List<String> csorts2 = this.sorts.get(name2);
        if (csorts1 == null) {
            this.addParseError(this.currentUseToken, ParseError.ERROR, "second id not declared");
            return false;
        }
        if (csorts2 == null) {
            this.addParseError(this.currentUseToken, ParseError.ERROR, "third id not declared");
            return false;
        }
        if (csorts1.size() != 2 || csorts1.get(1) != "univ") {
            this.addParseError(this.currentUseToken, ParseError.ERROR, "second id has incompatible sorts");
            return false;
        }
        if (csorts2.size() != 3 || csorts2.get(1) != "univ" || csorts2.get(2) != "univ") {
            this.addParseError(this.currentUseToken, ParseError.ERROR, "third id has incompatible sorts");
            return false;
        }
        if (this.allBuiltin.contains(name1)) {
            this.addParseError(this.currentUseToken, ParseError.ERROR, "second id is used in more than one 'use' declaration");
            return false;
        }
        if (this.allBuiltin.contains(name2)) {
            this.addParseError(this.currentUseToken, ParseError.ERROR, "third id is used in more than one 'use' declaration");
            return false;
        }
        this.allBuiltin.add(name1);
        this.allBuiltin.add(name2);
        return true;
    }

    private boolean check_sorts_two() {
        String name = this.builtinFuns.get(1);
        if (this.defs.contains(name)) {
            this.addParseError(this.currentUseToken, ParseError.ERROR, "second id cannot be defined symbol");
            return false;
        }
        List<String> csorts = this.sorts.get(name);
        if (csorts == null) {
            this.addParseError(this.currentUseToken, ParseError.ERROR, "second id not declared");
            return false;
        }
        if (csorts.size() != 3 || csorts.get(2) != "univ") {
            this.addParseError(this.currentUseToken, ParseError.ERROR, "second id has incompatible sorts");
            return false;
        }
        if (this.allBuiltin.contains(name)) {
            this.addParseError(this.currentUseToken, ParseError.ERROR, "second id is used in more than one 'use' declaration");
            return false;
        }
        return true;
    }

    @Override
    public void inARegularId(ARegularId node) {
        if (this.inUseDecl) {
            String name = this.chop(node);
            if (!this.funs.contains(name)) {
                this.addParseError(node.getRegularid(), ParseError.ERROR, "id not declared");
            } else {
                this.builtinFuns.add(name);
            }
        }
    }

    @Override
    public void inASpecialId(ASpecialId node) {
        if (this.inUseDecl) {
            this.addParseError(node.getSpecialid(), ParseError.ERROR, "integer ids cannot be used here");
        }
    }

    public Set<Equation> getE() {
        return this.E;
    }

    public Set<Rule> getS() {
        return this.S;
    }

}
