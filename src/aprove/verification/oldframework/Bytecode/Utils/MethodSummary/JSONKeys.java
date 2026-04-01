package aprove.verification.oldframework.Bytecode.Utils.MethodSummary;

public enum JSONKeys {
    Summaries,
    Class,
    Methods,
    Name,
    Descriptor,
    Static,
    Complexity,
    Cases,
    UpperTime,
    LowerTime,
    UpperSpace,
    LowerSpace,
    UpperSize,
    LowerSize,
    Modifies,
    Pos,
    Bound,
    Comments,
    Throws,
    AlwaysThrows,
    Predicate,
    Type,
    Var0,
    Var1,
    ResultingPredicates,
    RemovedPredicates,
    Join,
    MayBeEqual,
    Cyclic,
    NonTree,
    DefiniteReachability,
    ReachableTypes,
    From,
    To,
    Fields,
    Var,
    Reachable;

    @Override
    public String toString() {
        String res = super.toString();
        String fst = Character.toString(res.toCharArray()[0]);
        return res.replaceFirst(fst, fst.toLowerCase());
    }

}
