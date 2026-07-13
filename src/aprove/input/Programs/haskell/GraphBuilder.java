package aprove.input.Programs.haskell;

import aprove.verification.oldframework.Haskell.BasicTerms.Apply;
import aprove.verification.oldframework.Haskell.BasicTerms.Cons;
import aprove.verification.oldframework.Haskell.BasicTerms.Var;
import aprove.verification.oldframework.Haskell.Declarations.DataDecl;
import aprove.verification.oldframework.Haskell.Declarations.HaskellDecl;
import aprove.verification.oldframework.Haskell.Declarations.SynTypeDecl;
import aprove.verification.oldframework.Haskell.HaskellObject;
import aprove.verification.oldframework.Haskell.Modules.HaskellEntity;
import aprove.verification.oldframework.Haskell.Modules.TyConsEntity;
import aprove.verification.oldframework.Haskell.Modules.TySynEntity;
import aprove.verification.oldframework.Haskell.Typing.DataCon;

import java.util.*;
import java.util.stream.IntStream;



public class GraphBuilder {
    private final OccurrenceGraph graph;

    private final List<TyConsEntity> dataDecls;

    private final Set<String> datatypeNames;

    private Map<String, TyConsEntity> preludeTyCons;

    // should be read directly from Prelude
    private Set<String> preludeNames = new LinkedHashSet<>(Set.of(
            "IO", "Either", "IOResult", "FilePath", "Integer", "ReadS", "Obj", "ShowS",
            "Int", "Rational", "WHNF", "Maybe", "IOError", "Nat", "Float", "IOFinished", "HugsException",
            "IOErrorKind", "Char", "Ordering", "Double", "String", "AET", "Ratio"
    ));

    public record GraphBuilderResult (OccurrenceGraph graph, List<TyConsEntity> dataDecls) {}

    public GraphBuilder() {
        this.dataDecls = new ArrayList<>();
        this.datatypeNames = new HashSet<>();
        this.graph = new OccurrenceGraph();
    }

//    public OccurrenceGraph buildFromDataDecl(List<DataDecl> dataDecls, List<SynTypeDecl>  synTypeDecls, Map<String, TyConsEntity> preludeTyConsMap) {
//        this.preludeTyCons = preludeTyConsMap;
//        dataDecls.forEach(d -> datatypeNames.add(d.getDefType().getToken().getText()));
//        synTypeDecls.forEach(d -> datatypeNames.add(d.getDefType().getToken().getText()));
//        synTypeDecls.forEach(this::processSynTypes);
//        for (DataDecl d : dataDecls) {
//            processDataDecl(d, d.getDefType().getToken().getText());
//        }
//        return graph;
//    }
//
//    public OccurrenceGraph buildFromDataDecl(List<DataDecl> dataDecls, List<SynTypeDecl>  synTypeDecls) {
//        dataDecls.forEach(d -> datatypeNames.add(d.getDefType().getToken().getText()));
//        synTypeDecls.forEach(d -> datatypeNames.add(d.getDefType().getToken().getText()));
//        synTypeDecls.forEach(this::processSynTypes);
//        for (DataDecl d : dataDecls) {
//            processDataDecl(d, d.getDefType().getToken().getText());
//        }
//        return graph;
//    }

    public GraphBuilderResult buildFromTyConsEntity(List<TyConsEntity> dataDecls, List<TySynEntity> synTypeDecls) {
        this.dataDecls.addAll(dataDecls);

        for (TyConsEntity entity : dataDecls) {
            datatypeNames.add(entity.getModule().getName() + "." + entity.getName());
        }
        for (TySynEntity entity : synTypeDecls) {
            datatypeNames.add(entity.getModule().getName() + "." + entity.getName());
        }

        for (TySynEntity entity : synTypeDecls) {
            processSynTypes(entity);
        }

        for (TyConsEntity entity : dataDecls) {
            processDataDecl((DataDecl) entity.getValue(), entity.getModule().getName() + "." + entity.getName());
        }

        return new GraphBuilderResult(graph, this.dataDecls);
    }

    private record FunctionHeadAndParameters (HaskellObject head, List<HaskellObject> arguments) {}


//    replaces flattenApp
    private FunctionHeadAndParameters processApply (Apply function) {
        List<HaskellObject> arguments = new ArrayList<>();
        HaskellObject current = function;

        while (current instanceof Apply apply) {
            arguments.add(apply.getArgument());
            current = apply.getFunction();
        }

//      reverse inplace the arguments list
        int size = arguments.size();
        for (int i = 0, j = size - 1; i < j; i++, j--) {
            HaskellObject temp = arguments.get(i);
            arguments.set(i, arguments.get(j));
            arguments.set(j, temp);
        }

        return new FunctionHeadAndParameters(current, arguments);
    }

    private Map<String, Integer> getParamIndex(Apply apply){
        FunctionHeadAndParameters functionHeadAndParameters = processApply(apply);
        List<HaskellObject> arguments = functionHeadAndParameters.arguments;
        Map<String, Integer> paramIndex = new HashMap<>();
        for (int i = 0; i < arguments.size(); i++) {
            paramIndex.put(
                    ((Var) arguments.get(i)).getSymbol().toString(),
                    i
            );
        }
        return paramIndex;
    }

    private void processSynTypes(TySynEntity entity) {
        String currentDef = entity.getModule().getName() + "." + entity.getName();
        SynTypeDecl synTypeDecl = (SynTypeDecl) entity.getValue();
        Map<String, Integer> paramIndex = new LinkedHashMap<>();

        if (synTypeDecl.getDefType() instanceof Apply apply) {
            paramIndex = getParamIndex(apply);
        }

        graph.addNode(
                new OccurrenceGraph.DefNode(currentDef)
        );

        walkType(
                synTypeDecl.getType()
                , Occurrence.STRICT_POS
                , new OccurrenceGraph.DefNode(currentDef)
                , currentDef
                , paramIndex
        );

    }

    private void processDataDecl(DataDecl dd, String name) {
        //reset
        String currentDef = name;
        Map<String, Integer> paramIndex = new LinkedHashMap<>();

        if (dd.getDefType() instanceof Apply apply) {
            paramIndex = getParamIndex(apply);
        }
        //create node
        graph.addNode(
                new OccurrenceGraph.DefNode(currentDef)
        );

        for (DataCon ctor : dd.getDataCons()) {
            processConstructor(ctor, currentDef, paramIndex);
        }

    }

    /**
     * Collects arguments from a data declaration and returns the head of the function
     *
     * @param app  some Apply (e.g. Foo a b c)
     * @param args array storing the arguments (e.g. Foo a b c => args = [a, b, c]
     * @return head (Foo a b c => Foo)
     */
    private HaskellObject flattenApp(Apply app, List<HaskellObject> args) {
        List<HaskellObject> reversed = new ArrayList<>();
        HaskellObject current = app;

        while (current instanceof Apply apply) {
            reversed.add(apply.getArgument());
            current = apply.getFunction();
        }

        for (int i = reversed.size() - 1; i >= 0; i--) {
            args.add(reversed.get(i));
        }

        return current;
    }

    private void processConstructor(DataCon ctor, String currentDef, Map<String, Integer> paramIndex) {
        // e.g. data List a = Nil | Cons a (List a)
        // => ctor = `Cons a (List a)`
        // => ctor.getTypes() -> ['a', '(List a)']
        for (var type : ctor.getTypes()) {
            walkType(
                    type
                    , Occurrence.STRICT_POS
                    , new OccurrenceGraph.DefNode(currentDef)
                    , currentDef
                    , paramIndex
            );
        }
    }

    private void walkType(HaskellObject type, Occurrence pol, OccurrenceGraph.Node target, String currentDef, Map<String, Integer> paramIndex) {
        if (type instanceof Cons cons) {
            walkCons(cons, pol, target);
        } else if (type instanceof Var var) {
            walkVar(var, pol, target, currentDef, paramIndex);
        } else if (type instanceof Apply apply) {
            walkApply(apply, pol, target, currentDef, paramIndex);
        }
    }

    // e.g. Foo = mkFoo Bar => cons -> `Bar`
    private void walkCons(Cons cons, Occurrence pol, OccurrenceGraph.Node target) {
        String name = cons.getSymbol().getEntity().getModule().getName() + "." + cons.getSymbol().toString();
        if (datatypeNames.contains(name)) {
            graph.addEdge(
                    new OccurrenceGraph.DefNode(name),
                    target,
                    pol
            );
//        } else if (preludeTyCons != null && preludeTyCons.containsKey(name)) {
//            TyConsEntity entity = preludeTyCons.get(name);
//            if (entity.getValue() instanceof SynTypeDecl synTypeDecl) {
//                walkType(synTypeDecl.getType(), pol, target);
//            } else if (entity.getValue() instanceof DataDecl dataDecl) {
//                processDataDecl(dataDecl, name);
//            }
        } else {
            datatypeNames.add(name);
            HaskellDecl decl = (HaskellDecl) cons.getSymbol().getEntity().getValue();
            if (decl instanceof DataDecl dataDecl) {
                this.dataDecls.add((TyConsEntity) cons.getSymbol().getEntity());
                processDataDecl(dataDecl, name);
            } else if (decl instanceof SynTypeDecl synTypeDecl) {
                processSynTypes((TySynEntity) cons.getSymbol().getEntity());
            }
            graph.addEdge(
                    new OccurrenceGraph.DefNode(name),
                    target,
                    pol
            );
        }
    }

    private void walkVar(Var var, Occurrence pol, OccurrenceGraph.Node target, String currentDef, Map<String, Integer> paramIndex) {
        String name = var.getSymbol().toString();
        if (paramIndex.containsKey(name)) {
            int index = paramIndex.get(name);
            graph.addEdge(
                    new OccurrenceGraph.ArgNode(currentDef, index),
                    target,
                    pol
            );
        }
    }


    private void walkApply(Apply apply, Occurrence pol, OccurrenceGraph.Node target, String currentDef, Map<String, Integer> paramIndex) {

        FunctionHeadAndParameters functionHeadAndParameters = processApply(apply);
        HaskellObject head = functionHeadAndParameters.head;
        List<HaskellObject> args = functionHeadAndParameters.arguments;

        if (head instanceof Cons cons) {

            String name = cons.getSymbol().getEntity().getModule().getName() + "." + cons.getSymbol().toString();

            //check if arrow function
            if (name.equals("Prelude.->")) {
                walkArrow(apply, pol, target, currentDef, paramIndex);
                return;
            }


            if (datatypeNames.contains(name)) {
                graph.addEdge(
                        new OccurrenceGraph.DefNode(name),
                        target,
                        pol
                );
            }

            for (int i = 0; i < args.size(); i++) {
                Occurrence argPol = pol.otimes(argPolarity(name));
                var argTarget = argTarget(name, i, target);
                walkType(args.get(i), argPol, argTarget, currentDef, paramIndex);
            }
        } else if (head instanceof Var var) {
            String name = var.getSymbol().toString();
            walkType(head, pol, target, currentDef, paramIndex);
            if (paramIndex.containsKey(name)) {
                int index = paramIndex.get(name);
                target = new OccurrenceGraph.ArgNode(currentDef, index);
            }
            for (var a : args) {
                walkType(a, pol.otimes(Occurrence.MIXED), target, currentDef, paramIndex);
            }
        } else {
            walkType(head, pol, target, currentDef, paramIndex);
            for (var a : args) {
                walkType(a, pol.otimes(Occurrence.MIXED), target, currentDef, paramIndex);
            }
        }
    }

    private Occurrence argPolarity(String name) {
        if (datatypeNames.contains(name) || preludeNames.contains(name)) {
//            return Occurrence.GUARD_POS;
            return Occurrence.STRICT_POS;
        }
        return Occurrence.MIXED;
    }

    private OccurrenceGraph.Node argTarget(
            String name, int argIndex, OccurrenceGraph.Node currentTarget
    ) {
        if (datatypeNames.contains(name) || preludeNames.contains(name)) {
            return new OccurrenceGraph.ArgNode(name, argIndex);
        }
        return currentTarget;
    }

    private void walkArrow(Apply apply, Occurrence pol, OccurrenceGraph.Node target, String currentDef, Map<String, Integer> paramIndex) {
        var codomain = apply.getArgument();
        if (apply.getFunction() instanceof Apply apply2) {
            var domain = apply2.getArgument();
            walkType(domain, pol.otimes(Occurrence.JUST_NEG), target, currentDef, paramIndex);
            walkType(codomain, pol, target, currentDef, paramIndex);
        } else {
            //should not happen
        }
    }
}
