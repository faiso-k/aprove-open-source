/**
 *
 */
package aprove.input.Programs.xtc;

public enum XTCTagNames {
    arg, arity, author, automaton, automatonstuff, booleans, cast, comment,
    condition, conditions, conditiontype, constructor_based, date, div, entry,
    equals, full, funapp, funcsym, greater_equals, greater_than, integers,
    less_equals, less_than, lhs, logical_and, logical_not, logical_or,
    logical_than, logicaldomain, lowerbound, maybe, metainformation, minus,
    modulo, name, naturals, no, not_equals, originalfilename,
    plus, problem, relrules, replacementmap, rhs, rule, rules, semantics,
    signature, startterm, status, strategy, theory, times, trs, u_minus,
    upperbound, var, yes;
    public static XTCTagNames fromString(String s) {
        return XTCTagNames.valueOf(s.replace('-', '_'));
    }
}