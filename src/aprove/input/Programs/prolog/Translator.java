package aprove.input.Programs.prolog;

import java.io.*;
import java.util.*;

import aprove.*;
import aprove.input.Generated.prolog.lexer.*;
import aprove.input.Generated.prolog.node.*;
import aprove.input.Generated.prolog.parser.*;
import aprove.input.Programs.prolog.structure.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Prolog Translator for reading and parsing Prolog files.<br>
 * <br>
 * Created: 01.03.2006<br>
 * Last modified: 03.05.2012
 * @author cryingshadow
 * @version $Id$
 */
public class Translator extends aprove.verification.oldframework.Input.Translator.TranslatorSkeleton {

    /**
     * Parses a single clause.
     * @param clause A String representing a clause.
     * @return The parsed clause.
     * @throws TranslationException If it cannot be translated (I guess).
     */
    public static PrologClause parseClause(final String clause) throws TranslationException {
        final Translator tr = new Translator();
        PrologClause result = null;
        tr.translate(clause);
        if (tr.getProgram().getClauses().size() != 1) {
            throw new IllegalArgumentException("The String may only contain one clause!");
        }
        result = tr.getProgram().getClauses().get(0);
        return result;
    }

    /**
     * Parses the given Strings to extract queries.
     * @param layout The Strings to parse.
     * @return A set of the parsed queries.
     */
    public static Set<PrologQuery> parseQueries(final List<String> layout) {
        return Translator.parseQueries(layout, true);
    }

    /**
     * Parses the given Strings to extract a single query.
     * @param layout The Strings to parse.
     * @return A single parsed query or null if there is not exactly one query to parse in the specified Strings.
     */
    public static PrologQuery parseQuery(final List<String> layout) {
        return Translator.parseQuery(layout, true);
    }

    /**
     * Parses the given String to extract a single query.
     * @param query The String to parse.
     * @return A single parsed query or null if there is not exactly one query to parse in the specified String.
     */
    public static PrologQuery parseQuery(final String query) {
        return Translator.parseQuery(Collections.singletonList(query));
    }

    /**
     * Returns the query specified by the given term (if the given term does specify a query).
     * @param term The term in question to specify a query.
     * @param purpose The purpose of the resulting query.
     * @return The query specified by the given term or null if the term does not specify a query.
     */
    public static PrologQuery toQuery(final PrologTerm term, final PrologPurpose purpose) {
        final Moding[] mode = new Moding[term.getArity()];
        boolean correct = true;
        for (int i = 0; i < mode.length; i++) {
            final String name = term.getArgument(i).getName().toLowerCase().trim();
            final Moding parsed = Translator.parseModing(name);
            if (parsed == null) {
                correct = false;
                break;
            } else {
                mode[i] = parsed;
            }
        }
        if (correct) {
            return new PrologQuery(term.getName(), mode, purpose);
        } else {
            return null;
        }
    }

    //    /**
    //     * Parses the given Strings to extract queries and adds them to the specified Prolog program.
    //     * @param program The Prolog program.
    //     * @param layout The Strings to parse.
    //     */
    //    public void parseAndAddQueries(final PrologProgram program, final List<String> layout) {
    //        this.getQueries().addAll(Translator.parseQueries(layout, true));
    //    }

    /**
     * Parses the given Strings to extract an Afs.
     * @param layout The Strings to parse.
     * @return The parsed Afs.
     */
    private static Afs parseAfs(final List<String> layout) {
        final Afs res = new Afs();
        for (final Pair<String, YNM[]> pair : Translator.parseAfsHelper(layout)) {
            res.setFiltering(FunctionSymbol.create(pair.x, pair.y.length), pair.y);
        }
        return res;
    }

    /**
     * Parses the given Strings to extract Afss.
     * @param layout The Strings to parse.
     * @return A set of pairs of Strings and YNM arrays which can be used to construct Afss or queries.
     */
    private static Set<Pair<String, YNM[]>> parseAfsHelper(final List<String> layout) {
        final Set<Pair<String, YNM[]>> res = new LinkedHashSet<Pair<String, YNM[]>>();
        for (final String text : layout) {
            boolean initial = true;
            int pos = text.indexOf("afs:");
            AfsLoop: while (pos > 0) {
                int counter = 1;
                char c = text.charAt(pos - counter);
                while (initial && c != '%') {
                    if (c != ' ' || pos - counter <= 0) {
                        pos = text.indexOf("afs:", pos + 4);
                        initial = true;
                        continue AfsLoop;
                    }
                    counter++;
                    c = text.charAt(pos - counter);
                }
                pos += 4;
                final int slash = text.indexOf('/', pos);
                final int lf = text.indexOf('\n', pos);
                if (slash > pos && (lf < 0 || slash < lf)) {
                    final String name = text.substring(pos, slash).trim();
                    final int gleich = text.indexOf('=', slash + 1);
                    if (gleich > slash + 1 && (lf < 0 || gleich < lf)) {
                        int arity = 0;
                        try {
                            arity = Integer.parseInt(text.substring(slash + 1, gleich).trim());
                        } catch (final NumberFormatException e) {
                            pos = text.indexOf("afs:", pos);
                            initial = true;
                            continue AfsLoop;
                        }
                        final int listOpen = text.indexOf('{', gleich + 1);
                        if (listOpen > gleich && (lf < 0 || listOpen < lf)) {
                            final int listClose = text.indexOf('}', listOpen + 1);
                            if (listClose > listOpen && (lf < 0 || listClose < lf)) {
                                final String[] list = text.substring(listOpen + 1, listClose).trim().split(",");
                                if (list.length == 1 && "".equals(list[0])) {
                                    final YNM[] mode = new YNM[arity];
                                    for (int i = 0; i < arity; i++) {
                                        mode[i] = YNM.NO;
                                    }
                                    res.add(new Pair<String, YNM[]>(name, mode));
                                    if (text.length() > listClose + 1 && text.charAt(listClose + 1) == ',') {
                                        pos = listClose - 2;
                                        initial = false;
                                        continue AfsLoop;
                                    }
                                } else {
                                    final int[] values = new int[list.length];
                                    for (int i = 0; i < values.length; i++) {
                                        try {
                                            values[i] = Integer.parseInt(list[i]);
                                        } catch (final NumberFormatException e) {
                                            if (text.length() > listClose + 1 && text.charAt(listClose + 1) == ',') {
                                                pos = listClose - 2;
                                                initial = false;
                                            } else {
                                                pos = text.indexOf("afs:", pos);
                                                initial = true;
                                            }
                                            continue AfsLoop;
                                        }
                                        if (i > 0 && values[i - 1] >= values[i]) {
                                            if (text.length() > listClose + 1 && text.charAt(listClose + 1) == ',') {
                                                pos = listClose - 2;
                                                initial = false;
                                            } else {
                                                pos = text.indexOf("afs:", pos);
                                                initial = true;
                                            }
                                            continue AfsLoop;
                                        }
                                    }
                                    final YNM[] mode = new YNM[arity];
                                    int j = 0;
                                    for (int i = 0; i < arity; i++) {
                                        mode[i] = j < values.length && values[j] == i + 1 ? YNM.YES : YNM.NO;
                                        if (mode[i] == YNM.YES) {
                                            j++;
                                        }
                                    }
                                    res.add(new Pair<String, YNM[]>(name, mode));
                                    if (text.length() > listClose + 1 && text.charAt(listClose + 1) == ',') {
                                        pos = listClose - 2;
                                        initial = false;
                                        continue AfsLoop;
                                    }
                                }
                            }
                        }
                    }
                }
                pos = text.indexOf("afs:", pos);
                initial = true;
            }
        }
        return res;
    }

    /**
     * Parses the given String as a moding indicator.
     * @param name The String to parse.
     * @return The parsed moding indicator or null if the String does not represent one.
     */
    private static Moding parseModing(final String name) {
        if ("g".equals(name) || "i".equals(name) || "b".equals(name)) {
            return Moding.GROUND;
        } else if ("a".equals(name) || "o".equals(name) || "f".equals(name)) {
            return Moding.ANY;
        } else if ("n".equals(name)) {
            return Moding.NUMBER;
        } else {
            return null;
        }
    }

    /**
     * Parses the given Strings to extract queries for the specified purpose.
     * @param layout The Strings to parse.
     * @param parseAfs Flag to indicate whether old query format (AFSs) should also be accepted.
     * @return A set of the parsed queries.
     */
    private static Set<PrologQuery> parseQueries(final List<String> layout, final boolean parseAfs) {
        final Set<PrologQuery> res = new LinkedHashSet<PrologQuery>();
        if (parseAfs) {
            for (final Pair<String, YNM[]> pair : Translator.parseAfsHelper(layout)) {
                res.add(new PrologQuery(pair.x, pair.y, PrologPurpose.TERMINATION));
            }
        }
        /*
         * The queries for the PrologProblem have to be extracted from
         * the layout text.
         */
        for (final String text : layout) {
            res.addAll(Translator.parseQueries(text, "query:", PrologPurpose.TERMINATION));
            res.addAll(Translator.parseQueries(text, "complexity:", PrologPurpose.COMPLEXITY));
            res.addAll(Translator.parseQueries(text, "determinacy:", PrologPurpose.DETERMINACY));
        }
        return res;
    }

    /**
     * Parses the given String to extract queries starting with the specified pattern for the specified purpose.
     * @param text The String to parse.
     * @param pattern The pattern indicating the start of the query.
     * @param purpose The purpose of the query.
     * @return A set of the parsed queries.
     */
    private static Set<PrologQuery> parseQueries(final String text, final String pattern, final PrologPurpose purpose) {
        final Set<PrologQuery> res = new LinkedHashSet<PrologQuery>();
        final int patternLength = pattern.length();
        int pos = text.indexOf(pattern);
        QueryLoop: while (pos > 0) {
            int counter = 1;
            char c = text.charAt(pos - counter);
            while (c != '%') {
                if (c != ' ' || pos - counter <= 0) {
                    pos = text.indexOf(pattern, pos + patternLength);
                    continue QueryLoop;
                }
                counter++;
                c = text.charAt(pos - counter);
            }
            pos += patternLength;
            final int openP = text.indexOf('(', pos);
            final int lf = text.indexOf('\n', pos);
            if (openP > pos && (lf < 0 || openP < lf)) {
                final String name = text.substring(pos, openP).trim();
                final int closeP = text.indexOf(')', openP + 1);
                if (closeP > openP && (lf < 0 || closeP < lf)) {
                    final String[] list = text.substring(openP + 1, closeP).trim().split(",");
                    final Moding[] mode = new Moding[list.length];
                    for (int i = 0; i < mode.length; i++) {
                        final String check = list[i].trim().toLowerCase();
                        final Moding parsed = Translator.parseModing(check);
                        if (parsed == null) {
                            if (text.length() > closeP + 1 && text.charAt(closeP + 1) == ',') {
                                pos = closeP - patternLength + 2;
                                continue QueryLoop;
                            }
                            pos = text.indexOf(pattern, pos);
                            continue QueryLoop;
                        } else {
                            mode[i] = parsed;
                        }
                    }
                    res.add(new PrologQuery(name, mode, purpose));
                    if (text.length() > closeP + 1 && text.charAt(closeP + 1) == ',') {
                        pos = closeP - patternLength + 2;
                        continue QueryLoop;
                    }
                }
            } else if ((lf > pos && openP > lf) || (openP < 0 && (lf < 0 || lf > pos))) {
                String name;
                if (lf < 0) {
                    name = text.substring(pos).trim();
                } else {
                    name = text.substring(pos, lf).trim();
                }
                if (name.indexOf(' ') < 0) {
                    if (name.endsWith(".")) {
                        name = name.substring(0, name.length() - 1);
                    }
                    res.add(new PrologQuery(name, new Moding[0], purpose));
                }
            }
            pos = text.indexOf(pattern, pos);
        }
        return res;
    }

    /**
     * @param layout
     * @param parseAfs
     * @return
     */
    private static PrologQuery parseQuery(final List<String> layout, final boolean parseAfs) {
        final Set<PrologQuery> set = Translator.parseQueries(layout, parseAfs);
        if (set != null && !set.isEmpty()) {
            if (Globals.useAssertions) {
                assert set.size() == 1 : "Multiple queries occurred!";
            }
            return set.iterator().next();
        } else {
            return null;
        }
    }

    /**
     * The parsed argument filtering system.
     */
    private Afs afs;

    /**
     * The parsed PrologProgram.
     */
    private PrologProgram program;

    /**
     * The parsed query.
     */
    private PrologQuery query;

    /**
     * The parsed triples.
     */
    private PrologProgram triples;

    /**
     * Standard constructor.
     */
    public Translator() {
        this.program = null;
        this.triples = null;
        this.afs = null;
    }

    /**
     * @return The Afs.
     */
    public Afs getAfs() {
        return this.afs;
    }

    @Override
    public Language getLanguage() {
        return Language.PROLOG;
    }

    /**
     * Returns the parsed PrologProgram if the Prolog file could be parsed
     * correctly. Otherwise null is returned.
     * @return The parsed PrologProgram.
     */
    public PrologProgram getProgram() {
        return this.program;
    }

    /**
     * @return The query.
     */
    public PrologQuery getQuery() {
        return this.query;
    }

    /**
     * @return The parsed triples.
     */
    public PrologProgram getTriples() {
        return this.triples;
    }

    /**
     * Parses the Prolog file specified by the given Reader. The parsed PrologProgram can be read by the getProgram()
     * method afterwards.
     * @param reader The reader of the Prolog file to parse.
     * @throws TranslationException If any exception is thrown during the parsing process.
     */
    public void lexAndParse(final Reader reader) throws TranslationException {
        this.query = Translator.parseQuery(this.lexAndParseProgramAndLayout(reader, false));
        this.setState(new ParsedProlog(this.program, this.query));
    }

    /**
     * Parses the Prolog file specified by the given Reader as a dependency triple problem. The parsed PrologPrograms
     * can be read by the getProgram() method for the program clauses and by the getTriples() method for the triple
     * clauses afterwards.
     * @param reader The reader of the Prolog file to parse.
     * @throws TranslationException If any exception is thrown during the parsing process.
     */
    public void lexAndParseTriples(final Reader reader) throws TranslationException {
        final List<String> layout = this.lexAndParseProgramAndLayout(reader, true);
        this.query = Translator.parseQuery(layout, false);
        this.setState(new ParsedProlog(this.program, this.query));
        this.afs = Translator.parseAfs(layout);
    }

    /**
     * Parses the Prolog file specified by the given Reader. The parsed PrologProgram can be read by the getProgram()
     * method afterwards. Moreover, corresponding queries are parsed as an Afs, which can be accessed by the getAfs()
     * method afterwards.
     * @param reader The reader of the Prolog file to parse.
     * @throws TranslationException If any exception is thrown during the parsing process.
     */
    public void lexAndParseWithAfs(final Reader reader) throws TranslationException {
        final List<String> layout = this.lexAndParseProgramAndLayout(reader, false);
        this.query = Translator.parseQuery(layout, false);
        this.setState(new ParsedProlog(this.program, this.query));
        this.afs = Translator.parseAfs(layout);
    }

    @Override
    public void translate(final File file) throws FileNotFoundException, TranslationException {
        final Reader reader = new InputStreamReader(new FileInputStream(file));
        this.translate(reader);
    }

    @Override
    public void translate(final Reader reader) throws TranslationException {
        this.lexAndParse(reader);
    }

    /**
     * Translate to a dependency triple problem using the given file as source.
     * @param file The file to parse.
     * @throws FileNotFoundException If the file does not exist.
     * @throws TranslationException If any exception occurs during the parsing process.
     */
    public void translateTriples(final File file) throws FileNotFoundException, TranslationException {
        final Reader reader = new InputStreamReader(new FileInputStream(file));
        this.translateTriples(reader);
    }

    /**
     * Translate to a dependency triple problem using the given reader as source.
     * @param reader The reader giving the text to parse.
     * @throws TranslationException If any exception occurs during the parsing process.
     */
    public void translateTriples(final Reader reader) throws TranslationException {
        this.lexAndParseTriples(reader);
    }

    /**
     * Read the file into a String, wrap a PushbackReader around the String, and then parse the program from that
     * PushbackReader.
     * @param reader The reader of the Prolog file to parse.
     * @param triples Flag indicating whether or not to interpret the program as a dependency triple problem.
     * @return A list of layout Strings possibly containing queries.
     * @throws TranslationException If any exception occurs during the parsing process.
     */
    private List<String> lexAndParseProgramAndLayout(final Reader reader, final boolean triples)
        throws TranslationException
    {
        final StringBuffer buffer = new StringBuffer();
        final char[] input = new char[5120];
        int read;
        try {
            read = reader.read(input);
        } catch (final IOException e) {
            throw new TranslationException(e);
        }
        while (read != -1) {
            buffer.append(input, 0, read);
            try {
                read = reader.read(input);
            } catch (final IOException e) {
                throw new TranslationException(e);
            }
        }
        buffer.append("\n");
        final Reader newReader = new StringReader(buffer.toString());
        // 2^14 = 16384
        final PushbackReader pbr = new PushbackReader(newReader, 16384);
        final Lexer lexer = new Lexer(pbr);
        final Parser parser = new Parser(lexer);
        Start tree;
        try {
            tree = parser.parse();
        } catch (final ParserException | LexerException | IOException e) {
            throw new TranslationException(e);
        }
        if (triples) {
            final TriplePass pass = new TriplePass();
            tree.apply(pass);
            this.program = PrologParser.parse(pass.getClauseRoot(), pass.getOperatorSet());
            this.triples = PrologParser.parse(pass.getTripleRoot(), pass.getOperatorSet());
            return pass.getLayout();
        } else {
            final LayoutPass pass1 = new LayoutPass();
            final PreParsePass pass2 = new PreParsePass();
            tree.apply(pass1);
            tree.apply(pass2);
            this.program = PrologParser.parse(pass2.getRoot(), pass2.getOperatorSet());
            return pass1.getLayout();
        }
    }

}
