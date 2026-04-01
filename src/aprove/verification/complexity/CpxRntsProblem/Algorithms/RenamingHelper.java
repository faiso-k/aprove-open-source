package aprove.verification.complexity.CpxRntsProblem.Algorithms;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import aprove.verification.complexity.CpxIntTrsProblem.Exceptions.*;
import aprove.verification.complexity.CpxRntsProblem.*;
import aprove.verification.complexity.CpxRntsProblem.Structures.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Helper class to normalize function/variable names for external tools (e.g. KoAT)
 *  - renames function symbols and variables to match a given regex (should allow digits)
 *  - ensures free variables are not shared between rules by renaming (KoAT has some issues there)
 *  - can ensure correct case (upper case for variables, lower case for functions (for CoFloCo)
 *  - avoids some reserved names
 *
 * @author mnaaf
 */
public class RenamingHelper {
    private static final String ALLOWED_NAME_REGEX = "[A-Za-z][A-Za-z0-9_']*";
    private static final String ALPHA_NAME_REGEX = "[A-Za-z][A-Za-z0-9]*";
    private static final Set<String> BAD_NAMES = new HashSet<String>(Arrays.asList("nat", "pow"));

    private final Map<String,String> normalizedNames;
    private final FreshNameGenerator fng;
    private final CpxRntsProblem rnts;
    private final boolean caseSensitive;
    private final boolean alphaNumeric;

    private RenamingHelper(CpxRntsProblem rnts, boolean cs, boolean an) {
        this.normalizedNames = new HashMap<>();
        this.rnts = rnts;
        this.caseSensitive = cs;
        this.alphaNumeric = an;
        //use own fng to ensure it creates valid names
        this.fng = new FreshNameGenerator(rnts.getVariables(), FreshNameGenerator.APPEND_NUMBERS);
        this.fng.lockNames(CollectionUtils.getNames(rnts.getDefinedSymbols()));
    }

    private boolean isAllowed(String name) {
        if (BAD_NAMES.contains(name)) return false;
        if (alphaNumeric && !name.matches(ALPHA_NAME_REGEX)) return false;
        return name.matches(ALLOWED_NAME_REGEX);
    }

    private String normalizeVarName(String name) {
        assert !name.isEmpty();
        if ((!this.caseSensitive || Character.isUpperCase(name.charAt(0)))
                && isAllowed(name)) {
            return name;
        }
        if (this.normalizedNames.containsKey(name)) {
            return this.normalizedNames.get(name);
        }
        String res = this.fng.getFreshName("V", false);
        normalizedNames.put(name, res);
        return res;
    }

    private String normalizeFunName(String name) {
        assert !name.isEmpty();
        if ((!this.caseSensitive || Character.isLowerCase(name.charAt(0)))
                && isAllowed(name)) {
            return name;
        }
        if (this.normalizedNames.containsKey(name)) {
            return this.normalizedNames.get(name);
        }
        String res = this.fng.getFreshName("fun", false);
        normalizedNames.put(name, res);
        return res;
    }

    private TRSFunctionApplication normalizeFunapp(TRSFunctionApplication funapp) {
        FunctionSymbol sym = funapp.getRootSymbol();
        if (this.rnts.isDefinedSymbol(sym)) {
            //if not defined symbol, we have COM_n or arithmetic which must be kept
            String symname = normalizeFunName(sym.getName());
            sym = FunctionSymbol.create(symname, sym.getArity());
        }

        ArrayList<TRSTerm> args = new ArrayList<>();
        for (TRSTerm arg : funapp.getArguments()) {
            if (arg.isVariable()) {
                args.add(arg);
            } else {
                args.add(normalizeFunapp((TRSFunctionApplication)arg));
            }
        }
        return TRSTerm.createFunctionApplication(sym, args);
    }

    private RntsRule normalizeRule(RntsRule rule) {
        Map<TRSVariable,TRSTerm> subs = new HashMap<>();
        for (TRSVariable v : rule.getVariables()) {
            String newName = normalizeVarName(v.getName());
            if (!newName.equals(v.getName())) {
                subs.put(v, TRSTerm.createVariable(newName));
            }
        }
        if (!subs.isEmpty()) {
            try {
                rule = rule.applyIntegerSubstitution(TRSSubstitution.create(ImmutableCreator.create(subs)));
            } catch (NotRepresentableAsPolynomialException e) {
                throw new RuntimeException(); //internal error
            }
        }

        TRSFunctionApplication lhs = normalizeFunapp(rule.getLeft());
        TRSTerm rhs = rule.getRight();
        if (!rhs.isVariable()) {
            rhs = normalizeFunapp((TRSFunctionApplication)rule.getRight());
        }
        return RntsRule.createUnsafe(lhs, rhs, rule.getCost(), rule.getConstraints());
    }

    //renames all free variables by fresh (not neccessarily allowed) names, use normalizeRule afterwards
    private RntsRule renameFreeVars(RntsRule rule) {
        Map<TRSVariable,TRSTerm> subs = new HashMap<>();
        Set<TRSVariable> lhsVars = rule.getLeft().getVariables();
        for (TRSVariable v : rule.getVariables()) {
            if (!lhsVars.contains(v)) {
                subs.put(v, TRSTerm.createVariable(this.fng.getFreshName(v.getName(), false)));
            }
        }
        try {
            return rule.applyIntegerSubstitution(TRSSubstitution.create(ImmutableCreator.create(subs)));
        } catch (NotRepresentableAsPolynomialException e) {
            throw new RuntimeException(); //internal error (only var renaming)
        }
    }

    private void buildReverseMapping(Map<String,String> reverseMap) {
        reverseMap.clear();
        for (Entry<String,String> entry : normalizedNames.entrySet()) {
            assert !reverseMap.containsKey(entry.getValue());
            reverseMap.put(entry.getValue(), entry.getKey());
        }
    }

    //if reverseMap is not null, it will map noramlized names to the original ones
    public static CpxRntsProblem normalize(CpxRntsProblem rnts, boolean caseSensitive, boolean alphaNumeric, Map<String,String> reverseMap) {
        RenamingHelper rename = new RenamingHelper(rnts,caseSensitive,alphaNumeric);

        //normalize names in all rules
        Set<RntsRule> rules = new LinkedHashSet<>();
        for (RntsRule rule : rnts.getRules()) {
            rule = rename.renameFreeVars(rule);
            rules.add(rename.normalizeRule(rule));
        }
        //also normalize the initial symbols
        Set<FunctionSymbol> initial = new LinkedHashSet<>();
        for (FunctionSymbol fun : rnts.getInitialSymbols()) {
            String newName = rename.normalizeFunName(fun.getName());
            initial.add(FunctionSymbol.create(newName,fun.getArity()));
        }
        //collect mapping
        if (reverseMap != null) {
            rename.buildReverseMapping(reverseMap);
        }
        return rnts.cloneWithNewRules(ImmutableCreator.create(rules),ImmutableCreator.create(initial));
    }
}
