package aprove.input.Programs.intProg;

import java.io.*;
import java.util.*;
import java.util.Map.Entry;

import org.antlr.runtime.*;

import aprove.input.Generated.IntProg.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.IRSwT.*;
import aprove.verification.oldframework.IRSwT.IRSwTFormatTransformer.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Input.Translator.*;
import aprove.verification.oldframework.IntTRS.*;
//import aprove.input.Utility.*;
import immutables.*;

/**
 * Translator for C integer programs.
 * @author cryingshadow
 * @version $Id$
 */
public class Translator extends TranslatorSkeleton {

    /**
     * Test method to find duplicates in C integer programs.
     * @param args First argument contains the path to the programs.
     */
    public static void main(String[] args) {
        Map<String, IRSProblem> problems = new LinkedHashMap<String, IRSProblem>();
        List<String> list = new ArrayList<String>();
        for (File fileEntry : new File(args[0]).listFiles()) {
            String path = fileEntry.getAbsolutePath();
            System.out.println("Parsing " + path);
            Translator t = new Translator();
            try {
                t.translate(fileEntry);
                problems.put(path, (IRSProblem)t.getState());
                list.add(path);
            } catch (FileNotFoundException | TranslationException e) {
                e.printStackTrace();
            }
        }
        System.out.println();
        System.out.println();
        System.out.println("Parsed " + problems.size() + " problems.");
        System.out.println();
        System.out.println("Now checking for duplicates...");
        System.out.println();
        System.out.println();
        String[] array = list.toArray(new String[]{});
        Map<String, String> unionFind = new LinkedHashMap<String, String>();
        for (int i = 0; i < array.length - 1; i++) {
            for (int j = i + 1; j < array.length; j++) {
                String path1 = array[i];
                String path2 = array[j];
                System.out.println("Comparing " + path1 + " and " + path2 + "...");
                String s1 = Translator.find(path1, unionFind);
                String s2 = Translator.find(path2, unionFind);
                if (s1.equals(s2)) {
                    continue;
                }
                if (problems.get(path1).equalsModuloVariableRenaming(problems.get(path2))) {
                    unionFind.put(s1, s2);
                }
            }
        }
        System.out.println();
        System.out.println();
        System.out.println("Duplicate check complete.");
        if (unionFind.isEmpty()) {
            System.out.println("No duplicates found.");
        } else {
            System.out.println("Found the following duplicates:");
            System.out.println();
            System.out.println();
            // compress
            List<String> allKeys = new ArrayList<String>(unionFind.keySet());
            for (String key : allKeys) {
                Translator.find(key, unionFind);
            }
            Comparator<Map.Entry<String, String>> comp =
                new Comparator<Map.Entry<String,String>>() {

                    @Override
                    public int compare(Entry<String, String> o1, Entry<String, String> o2) {
                        return o1.getValue().compareTo(o2.getValue());
                    }

                };
            Set<Map.Entry<String, String>> set = new TreeSet<Map.Entry<String, String>>(comp);
            set.addAll(unionFind.entrySet());
            for (Map.Entry<String, String> entry : set) {
                System.out.println(entry.getKey() + " -> " + entry.getValue());
            }
        }
    }

    /**
     * Performs the find operation for a union-find structure with path compression.
     * @param key Some key.
     * @param unionFind The union-find structure.
     * @return The representing element for the specified key.
     */
    private static String find(String key, Map<String, String> unionFind) {
        String next = key;
        List<String> update = new ArrayList<String>();
        while (unionFind.containsKey(next)) {
            update.add(next);
            next = unionFind.get(next);
        }
        for (String toUpdate: update) {
            unionFind.put(toUpdate, next);
        }
        return next;
    }

    /**
     * The language parsed by this translator.
     */
    private final Language language = Language.INTTRS;

    @Override
    public Language getLanguage() {
        return this.language;
    }

    @Override
    public void translate(Reader reader) throws TranslationException {
        try {
            IntProgLexer lex = new IntProgLexer(new ANTLRReaderStream(reader));
            CommonTokenStream tokens = new CommonTokenStream(lex);
            IntProgParser parser = new IntProgParser(tokens);
            IRSProblem irs = parser.irs();
            Map<IGeneralizedRule,IGeneralizedRule> map = new HashMap<>();
            this.setState(
                new IRSProblem(
                    ImmutableCreator.create(
                        IRSwTFormatTransformer.transformRules(irs.getRules(), RoundingBehaviour.UNKNOWN, IDPPredefinedMap.DEFAULT_MAP, map)
                    ),
                    irs.getStartTerm()
                )
            );
        } catch (RecognitionException re) {
//            final ParseError pe = new ParseError();
//            pe.setLine(re.line);
//            pe.setColumn(re.charPositionInLine);
//            pe.setMessage(re.getMessage());
//            this.getErrors().add(pe);
            throw new TranslationException(re);
        } catch (IntProgParseException | IOException e) {
//            final ParseError pe = new ParseError();
//            pe.setMessage(e.getMessage());
//            this.getErrors().add(pe);
            throw new TranslationException(e);
        }
    }

}
