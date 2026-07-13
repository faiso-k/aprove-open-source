package aprove.input.Programs.haskell;

import aprove.verification.oldframework.Haskell.BasicTerms.Apply;
import aprove.verification.oldframework.Haskell.BasicTerms.Cons;
import aprove.verification.oldframework.Haskell.Declarations.DataDecl;
import aprove.verification.oldframework.Haskell.Declarations.HaskellDecl;
import aprove.verification.oldframework.Haskell.Declarations.SynTypeDecl;
import aprove.verification.oldframework.Haskell.Expressions.HaskellExp;
import aprove.verification.oldframework.Haskell.HaskellObject;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Modules.Module;
import aprove.verification.oldframework.Utility.GenericStructures.Pair;

import java.util.*;

public class PositivityChecker {

    private static String typeName(DataDecl decl) {
        return decl.getDefType().getToken().getText();
    }

    private Result computeResult(Modules mods) {

        final Map<String, Module> modMap = mods.getModMap();
        final List<HaskellEntity> decls = new ArrayList<>(List.of());

        for (var module : modMap.values()) {
            if (module.getName().equals("Prelude")) {
              continue;
            }
            decls.addAll(module.getNewExpEntities());
        }

        final List<TyConsEntity> dataDecl = new ArrayList<>();
        final List<TySynEntity> synTypeDecls = new ArrayList<>();
        for (HaskellEntity decl : decls) {
            if (decl instanceof TyConsEntity data) {
                dataDecl.add(data);
            } else if (decl instanceof TySynEntity synType) {
                synTypeDecls.add(synType);
            }
        }

        GraphBuilder testBuilder = new GraphBuilder();
        GraphBuilder.GraphBuilderResult graphBuilderResult = testBuilder.buildFromTyConsEntity(dataDecl, synTypeDecls);
        OccurrenceGraph graph = graphBuilderResult.graph();
        dataDecl.clear();
        dataDecl.addAll(graphBuilderResult.dataDecls());

        List<Violation> violations = new ArrayList<>();
        Map<String, Occurrence> selfLoops = new LinkedHashMap<>();

        for (TyConsEntity d : dataDecl) {
            var defNode = new OccurrenceGraph.DefNode(d.getModule().getName() + "." + d.getName());
            var loop = graph.transitiveOccurrence(defNode, defNode);
            selfLoops.put(d.getModule().getName() + "." + d.getName(), loop);

            if (loop.isNotStrictlyPositive()) {
                violations.add(new Violation(d, loop));
            }
        }

        return new Result(graph, violations, selfLoops);
    }

    public void check(Modules mods) throws StrictPositivityException {
        Result result = computeResult(mods);
        if (!result.isValid()) {
            StringBuilder sb = new StringBuilder();
            sb.append("Strict positivity check failed:\n");
            result.violations().forEach(v -> sb.append("  ").append(v).append("\n"));
            throw new StrictPositivityException(sb.toString());
        }
    }

    private void walkType(HaskellObject type){
        if (type instanceof Cons cons && cons.getSymbol().toString().equals("IOResult") && cons.getSymbol().getEntity().getModule().equals("Prelude")) throw new StrictPositivityException("IOResult type is not strictly positive");
        else if (type instanceof Apply apply) {
            walkType(apply.getFunction());
            walkType(apply.getArgument());
        }
    }

    public void checkForIOResult(Modules mods) {
        Module main = mods.getMainModule();
        List<Pair<HaskellObject, HaskellExp>> startTerms = mods.getStartTerms();
        for (Pair<HaskellObject, HaskellExp> startTerm : startTerms) {
            walkType(startTerm.getValue().getTypeTerm());
        }
        for (HaskellEntity entity : main.getExpEntities()) {
            if (entity.getName().equals("IOResult")) continue; // then it is user defined and was checked previously
            else if (entity instanceof ConsEntity consEntity) walkType(consEntity.getType());
            else if (entity instanceof VarEntity varEntity) walkType(varEntity.getValue().getTypeTerm());
        }
    }

    public record Violation(TyConsEntity datatype, Occurrence loopOccurrence) {
        @Override
        public String toString() {

            if (datatype.getModule().getName().equals("Main")) {
                return datatype.getName() + " at line " + datatype.getValue().getToken().getLine() + " is not strictly positive" +
                        " (self-loop polarity = " + loopOccurrence.toString() + ")";

            }
            return datatype.getName() + " in module " + datatype.getModule().getName() + " is not strictly positive" + " (self-loop polarity = " + loopOccurrence.toString() + ")";

        }

        public DataDecl decl() {
            return (DataDecl) datatype.getValue();
        }

        public Occurrence occ() {
            return loopOccurrence;
        }
    }

    public record Result(
            OccurrenceGraph graph,
            List<Violation> violations,
            Map<String, Occurrence> selfLoops
    ) {
        public boolean isValid() {
            return violations.isEmpty();
        }
    }
}
