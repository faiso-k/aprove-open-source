package aprove.verification.oldframework.Bytecode.Utils.MethodSummary;

import org.json.JSONArray;
import org.json.JSONObject;

import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

import java.util.*;
import java.util.stream.Collectors;

public class AnnotationCollection {
    public final List<List<String>> joiningStructures;
    public final List<List<String>> mayBeEqual;
    public final Set<Pair<String, Set<HeapEdge>>> cyclic;
    public final Set<String> nonTree;
    public final Set<Triple<String, Set<HeapEdge>, String>> definiteReachabilities;
    public final Set<Pair<String, Set<String>>> reachableTypes;

    public AnnotationCollection() {
        this(new ArrayList<>(), new ArrayList<>(), new HashSet<>(), new HashSet<>(), new HashSet<>(), new HashSet<>());
    }

    public AnnotationCollection(List<List<String>> joiningStructures,
                                List<List<String>> mayBeEqual,
                                Set<Pair<String, Set<HeapEdge>>> cyclic,
                                Set<String> nonTree,
                                Set<Triple<String, Set<HeapEdge>, String>> definiteReachabilities,
                                Set<Pair<String, Set<String>>> reachableTypes) {
        this.joiningStructures = joiningStructures;
        this.mayBeEqual = mayBeEqual;
        this.cyclic = cyclic;
        this.nonTree = nonTree;
        this.definiteReachabilities = definiteReachabilities;
        this.reachableTypes = reachableTypes;
    }

    public static AnnotationCollection parseFromJSONObject(JSONObject annotations) {
        List<List<String>> joiningStructures = new ArrayList<>();
        List<List<String>> mayBeEquals = new ArrayList<>();
        Set<Pair<String, Set<HeapEdge>>> cyclic = new LinkedHashSet<>();
        Set<String> nonTree = new LinkedHashSet<>();
        Set<Triple<String, Set<HeapEdge>, String>> definiteReachabilities = new HashSet<>();
        Set<Pair<String, Set<String>>> reachableTypes = new HashSet<>();

        if (annotations.has(JSONKeys.Join.toString())) {
            JSONArray eqClasses = annotations.getJSONArray(JSONKeys.Join.toString());
            for (Object e : eqClasses) {
                joiningStructures.add(JSONUtil.getStringList((JSONArray) e));
            }
        }
        if (annotations.has(JSONKeys.MayBeEqual.toString())) {
            JSONArray eqClasses = annotations.getJSONArray(JSONKeys.MayBeEqual.toString());
            for (Object e : eqClasses) {
                mayBeEquals.add(JSONUtil.getStringList((JSONArray) e));
            }
        }
        if (annotations.has(JSONKeys.Cyclic.toString())) {
            JSONObject cyclicObj = annotations.getJSONObject(JSONKeys.Cyclic.toString());
            cyclicObj.keys().forEachRemaining(name -> {
                Set<HeapEdge> fields = JSONUtil.getStringSet(cyclicObj.getJSONArray(name))
                                               .stream()
                                               .map(InstanceFieldEdge::createFromDotted)
                                               .collect(Collectors.toSet());
                cyclic.add(new Pair<>(name, fields));
            });
        }
        if (annotations.has(JSONKeys.NonTree.toString())) {
            nonTree.addAll(JSONUtil.getStringList(annotations.getJSONArray(JSONKeys.NonTree.toString())));
        }
        if (annotations.has(JSONKeys.DefiniteReachability.toString())) {
            JSONArray defReachabilitiesArray = annotations.getJSONArray(JSONKeys.DefiniteReachability.toString());
            for (Object e : defReachabilitiesArray) {
                JSONObject defReachability = (JSONObject) e;
                String from = defReachability.getString(JSONKeys.From.toString());
                String to = defReachability.getString(JSONKeys.To.toString());
                Set<HeapEdge>
                        fields =
                        defReachability.has(JSONKeys.Fields.toString()) ?
                        JSONUtil.getStringSet(defReachability.getJSONArray(JSONKeys.Fields.toString()))
                                .stream().map(InstanceFieldEdge::createFromDotted).collect(Collectors.toSet()) :
                        new LinkedHashSet<>();
                definiteReachabilities.add(new Triple<>(from, fields, to));
            }
        }
        if (annotations.has(JSONKeys.ReachableTypes.toString())) {
            JSONArray reachableTypesArr = annotations.getJSONArray(JSONKeys.ReachableTypes.toString());
            for (Object e : reachableTypesArr) {
                JSONObject reachableType = (JSONObject) e;
                String classname = reachableType.getString(JSONKeys.Var.toString());
                Set<String>
                        reachable =
                        JSONUtil.getStringSet(reachableType.getJSONArray(JSONKeys.Reachable.toString()));
                reachableTypes.add(new Pair<String, Set<String>>(classname, reachable));
            }
        }
        return new AnnotationCollection(joiningStructures,
                                        mayBeEquals,
                                        cyclic,
                                        nonTree,
                                        definiteReachabilities,
                                        reachableTypes);
    }
}
