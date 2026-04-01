package aprove.verification.oldframework.Bytecode.Utils.MethodSummary;

import org.json.JSONArray;
import org.json.JSONObject;
import org.json.JSONTokener;

import aprove.verification.oldframework.Bytecode.Natives.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.util.*;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

import static java.util.stream.Collectors.*;

public class JSONUtil {

    private JSONUtil() {
        throw new UnsupportedOperationException(this.getClass().getName() + " should not be instanciated");
    }

    public static JSONObject storeAsJSON(Collection<MethodSummary> summaries) {
        Function<MethodSummary, Pair<MethodSummary, Collection<String>>> pad = s -> new Pair<>(s, Collections.emptyList()); //silences eclipse
        return storeAsJSON(summaries.stream().map(pad));
    }

    public static JSONObject storeAsJSON(Stream<Pair<MethodSummary, Collection<String>>> summaries) {
        Map<ClassName, List<JSONObject>> map = summaries
                .collect(groupingBy(s -> s.x.getMethodIdentifier().getClassName(),
                                    mapping( s -> s.x.toJSON(s.y), toList())));
        JSONArray res = new JSONArray();
        map.forEach((className, list) -> res.put(new JSONObject().put(JSONKeys.Class.toString(), className.toString())
                                                                 .put(JSONKeys.Methods.toString(), new JSONArray(list.toArray()))));
        return new JSONObject().put(JSONKeys.Summaries.toString(), res);
    }

    public static List<String> getStringList(JSONArray strArr) {
        List<String> res = new ArrayList<>(strArr.length());
        for (Object e : strArr) {
            res.add((String) e);
        }
        return res;
    }

    public static Set<String> getStringSet(JSONArray strArr) {
        Set<String> res = new HashSet<>(strArr.length());
        for (Object e : strArr) {
            res.add((String) e);
        }
        return res;
    }

    public static Set<Pair<MethodSummary, List<String>>> loadFromJSON(String filename) throws FileNotFoundException {
        Set<Pair<MethodSummary, List<String>>> res = new LinkedHashSet<>();
        JSONTokener tok = new JSONTokener(new FileInputStream(new File(filename)));
        JSONObject json = new JSONObject(tok);
        JSONArray summaries = json.getJSONArray(JSONKeys.Summaries.toString());
        for (Object entry: summaries) {
            JSONObject jsonEntry = (JSONObject) entry;
            String summarizedClass = jsonEntry.getString(JSONKeys.Class.toString());
            JSONArray jsonFunctions = jsonEntry.getJSONArray(JSONKeys.Methods.toString());
            for (Object o: jsonFunctions) {
                JSONObject fct = (JSONObject) o;
                String name = fct.getString(JSONKeys.Name.toString());
                String descriptor = fct.getString(JSONKeys.Descriptor.toString());
                boolean isStatic = fct.getBoolean(JSONKeys.Static.toString());
                ParsedMethodDescriptor parsedDescriptor = new ParsedMethodDescriptor(descriptor);

                Set<ComplexitySummary> refinedComplexities = new LinkedHashSet<>();

                if (fct.has(JSONKeys.Cases.toString())) {
                    JSONArray cases = fct.getJSONArray(JSONKeys.Cases.toString());
                    for (Object refinementCaseObj : cases) {
                        ComplexitySummary caseSummary = ComplexitySummary.parseFromJSONObject((JSONObject) refinementCaseObj);
                        if (caseSummary.predicate != null) {
                            refinedComplexities.add(caseSummary);
                        }
                    }
                }

                ComplexitySummary complexity = ComplexitySummary.parseFromJSONObject(fct);

                List<String> comments;
                if (fct.has(JSONKeys.Comments.toString())) {
                    JSONArray jsonComments = fct.getJSONArray(JSONKeys.Comments.toString());
                    comments = StreamSupport.stream(jsonComments.spliterator(), false).map(Object::toString).collect(
                            Collectors.toList());
                } else {
                    comments = Collections.emptyList();
                }

                ClassName cn = ClassName.fromDotted(summarizedClass);
                MethodIdentifier mid = new MethodIdentifier(cn, name, parsedDescriptor);

                res.add(new Pair<>(new MethodSummary(isStatic, complexity, refinedComplexities, mid), comments));
            }
        }
        return res;
    }
}
