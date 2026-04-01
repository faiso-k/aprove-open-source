package aprove.input.Programs.Strategy;

import java.io.*;
import java.lang.reflect.*;
import java.util.*;
import java.util.Map.Entry;
import java.util.regex.*;

import org.antlr.runtime.*;

import aprove.input.Generated.Strategy.*;
import aprove.strategies.Parameters.*;

public class PropertiesToStrategy {
    private static final Pattern SPLIT_PAT = Pattern.compile("\\s*:\\s*");

    private Map<String, Parameters> defaults;
    private Queue<String> toDo = new LinkedList<String>();
    private Set<String> seen = new LinkedHashSet<String>();

    private RawModule module = new RawModule();
    private Map<String, ClassDeclaration> knowDecls = new HashMap<String, ClassDeclaration>();

    public PropertiesToStrategy() throws IOException {
        this.defaults = new HashMap<String, Parameters>();
        Properties defprops = Util.loadPropertyFile("defaults.properties");
        for(Entry<Object, Object> e: defprops.entrySet()) {
            String key = (String) e.getKey();
            String value = (String) e.getValue();
            this.defaults.put(key.toUpperCase(), PropertiesToStrategy.parameters(value));
        }
//        for(Map.Entry<String, Parameters> e: defaults.entrySet()) {
//            System.err.println(e.getKey() + " = " + e.getValue().toString());
//        }
    }

    public void run() throws IOException {
        Set<String> expected = new LinkedHashSet<String>(this.defaults.keySet());
        while(! this.toDo.isEmpty()) {
            String next = this.toDo.remove();
//            System.err.println("########## Generated from: " + next);
            Properties itsProps = Util.loadPropertyFile(next);
            HashMap<String, String> asMap = new LinkedHashMap<String, String>();
            this.sortInto(asMap, itsProps, next);
            for(Entry<String, String> e: asMap.entrySet()) {
                String key = e.getKey();
                String value = e.getValue();
                String[] pieces = this.splitAtColonsAndTrim(value);
                String className = pieces[0];
                Parameters defs = this.defaults.get(key.toUpperCase());
                expected.remove(key.toUpperCase());
                if (defs == null) {
//                    System.err.println("# missing default spec for " + key);
                    defs = Parameters.EMPTY;
                }
                ClassDeclaration decl = new ClassDeclaration(key, className, defs);
                Class<?> c;
                try {
                    c = Class.forName(className);
                } catch (ClassNotFoundException e1) {
//                    System.err.println("# Ignored " + key + " because I'm unable to find that class");
                    continue;
                }
                int modif = c.getModifiers();
                if (Modifier.isAbstract(modif) || Modifier.isInterface(modif)) {
//                    System.err.println("# Ignored " + key + " because it is abstract/interface");
                    continue;
                }
                ClassDeclaration previous = this.knowDecls.get(key.toUpperCase());
                if (previous != null) {
                    if (! previous.equals(decl)) {
                        System.err.println("Conflict in " + decl.name);
                    }
                    continue;
                }
//                System.err.println(decl);
                this.module.addDeclaration(decl);
                this.knowDecls.put(key.toUpperCase(), decl);
                for(int i=1; i<pieces.length; i++) {
                    this.addPropFile(pieces[i]);
                }
            }
        }
        System.out.println(new TreeSet<String>(this.seen).toString());
        //System.err.println("Unused defaults: "  + expected);
        this.module.print(System.out);
    }

    // Tries to put keys from property file into map, in the order they appeared in the properties file
    private void sortInto(HashMap<String, String> asMap, Properties itsProps,
            String next) throws IOException {
        Pattern pat = Pattern.compile("^\\s*(\\w+)\\s*=");
        InputStream stream = ParameterManager.class.getResourceAsStream("Properties/" + next);
        BufferedReader reader = new BufferedReader(new InputStreamReader(stream));
        String line;
        while( (line = reader.readLine()) != null) {
            Matcher matcher = pat.matcher(line);
            if (matcher.find()) {
                String key = matcher.group(1);
                asMap.put(key, itsProps.getProperty(key));
            }
        }
        assert asMap.size() == itsProps.size();
    }

    private void addPropFile(String name) {
        if (this.seen.contains(name)) {
            return;
        }
        this.toDo.add(name);
        this.seen.add(name);
    }

    private String[] splitAtColonsAndTrim(String all) {
        return PropertiesToStrategy.SPLIT_PAT.split(all.trim());
    }

    public static void main(String[] args) throws Exception {
        PropertiesToStrategy it = new PropertiesToStrategy();
        it.addPropFile("processors.properties");
        it.run();
    }

    public static Parameters parameters(String paramString) {
        CharStream input = new ANTLRStringStream(paramString);
        StrategyParser parser = PropertiesToStrategy.buildParser(input);
        try {
            return parser.params();
        } catch (RecognitionException e) {
            throw new StrategyParseException(e, parser);
        }
    }

    private static StrategyParser buildParser(CharStream input) {
        StrategyLexer lexer = new StrategyLexer(input);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        StrategyParser parser = new StrategyParser(tokens);
        return parser;
    }
}
