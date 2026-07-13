package aprove.input.Programs.haskell;

import aprove.verification.oldframework.Haskell.BasicTerms.Apply;
import aprove.verification.oldframework.Haskell.BasicTerms.Cons;
import aprove.verification.oldframework.Haskell.BasicTerms.Var;
import aprove.verification.oldframework.Haskell.Declarations.DataDecl;
import aprove.verification.oldframework.Haskell.Declarations.HaskellDecl;
import aprove.verification.oldframework.Haskell.Declarations.SynTypeDecl;
import aprove.verification.oldframework.Haskell.HaskellObject;
import aprove.verification.oldframework.Haskell.Modules.TyConsEntity;
import aprove.verification.oldframework.Haskell.Modules.TySynEntity;
import aprove.verification.oldframework.Haskell.Typing.DataCon;

import java.util.*;


public class GraphBuilder {
    private final OccurrenceGraph graph;

    private final List<TyConsEntity> dataDecls;

    private final Set<String> datatypeNames;

    public GraphBuilder() {
        this.dataDecls = new ArrayList<>();
        this.datatypeNames = new HashSet<>();
        this.graph = new OccurrenceGraph();
    }

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

    private FunctionHeadAndArguments processApply(Apply function) {
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

        return new FunctionHeadAndArguments(current, arguments);
    }

    /**
     * Returns map of every function parameter name with their respective position (e.g. data Foo a b => {'a' -> 0, 'b' -> 1})
     *
     * @param apply Haskell function
     * @return parameter indices
     */
    private Map<String, Integer> getParamIndex(Apply apply) {

        // get function arguments
        FunctionHeadAndArguments functionHeadAndArguments = processApply(apply);
        List<HaskellObject> arguments = functionHeadAndArguments.arguments;

        // initialise paramIndex
        Map<String, Integer> paramIndex = new HashMap<>();

        // add index for each argument
        for (int i = 0; i < arguments.size(); i++) {
            if (arguments.get(i) instanceof Var var) {
                paramIndex.put(var.getSymbol().toString(), i);
            } else {
                // should not happen
                throw new IllegalArgumentException("Expected Var in type parameters, but got: " + arguments.get(i));
            }
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

    private void processDataDecl(DataDecl dd, String currentDef) {
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
        } else {
            datatypeNames.add(name);
            HaskellDecl decl = (HaskellDecl) cons.getSymbol().getEntity().getValue();
            if (decl instanceof DataDecl dataDecl) {
                this.dataDecls.add((TyConsEntity) cons.getSymbol().getEntity());
                processDataDecl(dataDecl, name);
            } else if (decl instanceof SynTypeDecl) {
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

        FunctionHeadAndArguments functionHeadAndArguments = processApply(apply);
        HaskellObject head = functionHeadAndArguments.head;
        List<HaskellObject> args = functionHeadAndArguments.arguments;

        if (head instanceof Cons cons) {

            String name = cons.getSymbol().getEntity().getModule().getName() + "." + cons.getSymbol().toString();

            //check if arrow function
            if (name.equals("Prelude.->")) {
                walkArrow(apply, pol, target, currentDef, paramIndex);
                return;
            }

            walkType(head, pol, target, currentDef, paramIndex);

            if (datatypeNames.contains(name)) {
                graph.addEdge(
                        new OccurrenceGraph.DefNode(name),
                        target,
                        pol
                );
            } else {
                System.out.println("Warning: datatype " + name + " not found in datatypeNames");
            }

            for (int i = 0; i < args.size(); i++) {
                Occurrence argPol = pol.otimes(argPolarity(name));
                var argTarget = argTarget(name, i, target);
                walkType(args.get(i), argPol, argTarget, currentDef, paramIndex);
            }
        }  else {
            walkType(head, pol, target, currentDef, paramIndex);

           if (head instanceof Var var && paramIndex.containsKey(var.getSymbol().toString())) {
                int index = paramIndex.get(var.getSymbol().toString());
                target = new OccurrenceGraph.ArgNode(currentDef, index);
            }

            for (var a : args) {
                walkType(a, pol.otimes(Occurrence.MIXED), target, currentDef, paramIndex);
            }
        }
    }

    private Occurrence argPolarity(String name) {
        if (datatypeNames.contains(name)) {
            return Occurrence.STRICT_POS;
        }
        return Occurrence.MIXED; // should not happen
    }

    private OccurrenceGraph.Node argTarget(
            String name, int argIndex, OccurrenceGraph.Node currentTarget
    ) {
        if (datatypeNames.contains(name)) {
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
        }
    }

    public record GraphBuilderResult(OccurrenceGraph graph, List<TyConsEntity> dataDecls) {
    }

    private record FunctionHeadAndArguments(HaskellObject head, List<HaskellObject> arguments) {
    }
}
