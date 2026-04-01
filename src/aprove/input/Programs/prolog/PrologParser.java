package aprove.input.Programs.prolog;

import java.math.*;
import java.util.*;
import java.util.logging.*;

import aprove.input.Programs.prolog.nodes.*;
import aprove.input.Programs.prolog.structure.*;
import aprove.verification.oldframework.Utility.*;

/**
 * The PrologParser expects a preparsed kind of syntax tree which
 * is more likely an extended token list. In this token list some
 * simple structures like lists and grammar conditions in curly
 * brackets are preparsed and operator declarations are read and
 * removed from the token list. During the parsing process the
 * token list is transformed into a correct syntax tree first and
 * into a PrologProgram afterwards.<br><br>
 *
 * Created: 21.05.2006<br>
 * Last modified: 11.05.2011
 *
 * @author cryingshadow
 * @version $Id$
 */
public abstract class PrologParser {

    protected static Logger logger = Logger.getLogger("aprove.verification.dpframework.PROLOGProblem.Processors");

    /**
     * Builds paranthesis terms recursively out of tokens enclosed by an
     * opening and closing paranthesis.
     * @param children The token list.
     * @throws PrologSyntaxException If a paranthesis is not closed, not
     *                               opened or empty.
     * @throws IllegalStateException If the specified list is null.
     */
    private static void buildParenthesis(final List<InternalNode> children)
        throws PrologSyntaxException,
            IllegalStateException
    {
        if (children == null) {
            throw new IllegalStateException("List or grammar condition elements have been erased!");
        }
        final ArrayList<InternalNode> listcond = new ArrayList<InternalNode>();
        final ArrayList<InternalNode> paranthesis = new ArrayList<InternalNode>();
        final ArrayList<PunctuationNode> open = new ArrayList<PunctuationNode>();
        for (final InternalNode node : children) {
            if (node instanceof PunctuationNode) {
                if (node.getText().equals("(")) {
                    open.add((PunctuationNode) node);
                }
            } else if (node instanceof ListNode || node instanceof ConditionNode) {
                listcond.add(node);
            }
        }
        final ArrayList<PunctuationNode> work = new ArrayList<PunctuationNode>();
        for (int i = open.size() - 1; i >= 0; i--) {
            work.add(open.get(i));
        }
        for (final PunctuationNode left : work) {
            final int start = children.indexOf(left) + 1;
            InternalNode right = null;
            for (int i = start; i < children.size(); i++) {
                right = children.get(i);
                if (right instanceof PunctuationNode) {
                    if (((PunctuationNode) right).getText().equals(")")) {
                        break;
                    }
                }
                right = null;
            }
            if (right == null) {
                throw new PrologSyntaxException("Opened paranthesis is not closed again!("
                    + left.getLine()
                    + ", "
                    + left.getPos()
                    + ")");
            }
            final int fin = children.indexOf(right);
            for (int i = start; i < fin; i++) {
                paranthesis.add(children.get(i));
            }
            final ParanthesisNode newNode = new ParanthesisNode(left.getLine(), left.getPos());
            for (final InternalNode node : paranthesis) {
                newNode.addChild(node);
            }
            children.remove(left);
            children.removeAll(paranthesis);
            children.remove(right);
            children.add(start - 1, newNode);
            paranthesis.clear();
        }
        for (final InternalNode node : children) {
            if (node instanceof PunctuationNode) {
                if (node.getText().equals(")")) {
                    throw new PrologSyntaxException("Closing paranthesis was not opended before!("
                        + node.getLine()
                        + ", "
                        + node.getPos()
                        + ")");
                }
            } else if (node instanceof ParanthesisNode) {
                if (node.getChildren() == null || node.getChildren().size() == 0) {
                    throw new PrologSyntaxException("Empty paranthesis occured!("
                        + node.getLine()
                        + ", "
                        + node.getPos()
                        + ")");
                }
            }
        }
        for (final InternalNode n : listcond) {
            PrologParser.buildParenthesis(n.getChildren());
        }
    }

    /**
     * Checks whether or not the specified node is a correct sentence.
     * @param node The node to check.
     * @throws PrologSyntaxException If the node is no correct sentence.
     */
    private static void checkSentence(final InternalNode node) throws PrologSyntaxException {
        if (!(node instanceof TermNode || node instanceof ListNode || node instanceof ConditionNode)) {
            throw new PrologSyntaxException("Unexpected contents in sentence!("
                + node.getLine()
                + ", "
                + node.getPos()
                + ")");
        }
        if (node instanceof ListNode) {
            for (final InternalNode n : node.getChildren()) {
                PrologParser.checkSentence(n);
            }
        }
    }

    //    private static Pair<List<PrologTerm>, InternalNode> extractFirstList(
    //        InternalNode bodyNode
    //    ) {
    //        if (
    //                bodyNode instanceof ListNode ||
    //                bodyNode instanceof EmptyListNode ||
    //                bodyNode instanceof StringNode
    //        ) {
    //            return new Pair<List<PrologTerm>,InternalNode>(
    //                    toPrologTerms(bodyNode.getChildren()),
    //                    null
    //            );
    //        } else if (bodyNode instanceof TermNode) {
    //            String name = bodyNode.getText();
    //            int arity =
    //                bodyNode.getChildren() == null ?
    //                    0 : bodyNode.getChildren().size();
    //            if (name.equals("','") && arity == 2) {
    //                InternalNode firstArg = bodyNode.getChildren().get(0);
    //                if (
    //                        firstArg instanceof ListNode ||
    //                        firstArg instanceof EmptyListNode ||
    //                        firstArg instanceof StringNode
    //                ) {
    //                    return new Pair<List<PrologTerm>,InternalNode>(
    //                            toPrologTerms(firstArg.getChildren()),
    //                            bodyNode.getChildren().get(1)
    //                    );
    //                }
    //            }
    //        }
    //        return new Pair<List<PrologTerm>,InternalNode>(
    //                new ArrayList<PrologTerm>(),
    //                bodyNode
    //        );
    //    }

    private static List<String> extractVariableNames(final InternalNode node) {
        final List<String> res = new ArrayList<String>();
        if (node instanceof VarNode) {
            res.add(node.getText());
        }
        if (node.getChildren() != null) {
            for (final InternalNode n : node.getChildren()) {
                res.addAll(PrologParser.extractVariableNames(n));
            }
        }
        return res;
    }

    private static Set<String> gatherFunctionSymbolNames(final InternalNode node) {
        final Set<String> res = new LinkedHashSet<String>();
        res.add(node.getText());
        if (node.getChildren() != null) {
            for (final InternalNode child : node.getChildren()) {
                res.addAll(PrologParser.gatherFunctionSymbolNames(child));
            }
        }
        return res;
    }

    /**
     * Checks whether or not the specified sentence is a directive.
     * @param sentence The sentence to check.
     * @return True if it is a directive. False otherwise.
     */
    private static boolean isDirective(final SentenceNode sentence) {
        final InternalNode node = sentence.getChildren().get(0);
        if (node instanceof TermNode && (node.getText().equals(":-") || node.getText().equals("?-"))) {
            if (node.getChildren().size() == 1) {
                return true;
            }
        }
        return false;
    }

    /**
     * Parses the preparsed ProgramNode to a PrologProgram using the
     * specified PrologOperatorSet.
     * @param ROOT The root of the syntax tree / token list.
     * @param OPS The set of operator declarations.
     * @return The parsed PrologProgram
     * @throws PrologSyntaxException If a syntax error occurs.
     */
    public static PrologProgram parse(final ProgramNode ROOT, final PrologOperatorSet OPS) throws PrologSyntaxException
    {
        final PrologProgram program = new PrologProgram(OPS);
        // to separate directives from other clauses
        final List<PrologDirective> directives = program.getDirectives();

        // extract the sentences
        final ArrayList<SentenceNode> sentences = new ArrayList<SentenceNode>();
        for (final InternalNode node : ROOT.getChildren()) {
            sentences.add((SentenceNode) node);
        }

        // parse every sentence independent of all other sentences
        for (final SentenceNode sentence : sentences) {
            // get the token list
            final List<InternalNode> children = sentence.getChildren();
            if (children == null) {
                throw new PrologSyntaxException("Empty sentence occured!("
                    + sentence.getLine()
                    + ", "
                    + sentence.getPos()
                    + ")");
            }
            PrologParser.buildParenthesis(children);

            /*
             * Now some TreeWalkers are defined and applied to the
             * sentence afterwards. The several steps of parsing the
             * sentence are are performed by these TreeWalkers. The
             * TreeWalkers visit every node of the sentence and invoke
             * their action method with the visited node as its argument.
             */
            final TreeWalker walk1_buildNonOperatorTerms = new NonOpWalker(OPS);
            final TreeWalker walk2_buildOperatorTerms = new OpWalker(OPS);
            final TreeWalker walk3_cleanLayout = new CleanLayoutWalker();
            final TreeWalker walk4_cleanCommasAndLists = new CleanCommaListWalker();

            /*
             * At this point every paranthesis should contain exactly one
             * term. So all ParanthesisNodes can be removed. But before
             * this removal it must be checked if no precedence conflicts
             * occur in compound terms.
             */
            final TreeWalker walk5_cleanParanthesis = new CleanParanthesisWalker();

            /*
             * Finally all remaining possible syntax errors must be checked.
             * If no syntax errors occured during the parsing process, there
             * is no NameNode, ParanthesisNode or CommaNode left and every
             * SentenceNode has exactly one argument. Additionally every
             * TermNode has a list of arguments (which may be empty, but not
             * null) and TermNodes with a precedence greater than 0 must have
             * at least one argument.
             */
            final TreeWalker walk6_checkNodes = new CheckWalker();
            sentence.apply(walk1_buildNonOperatorTerms);
            sentence.applyFirst(walk2_buildOperatorTerms);
            sentence.apply(walk3_cleanLayout);
            sentence.apply(walk4_cleanCommasAndLists);
            sentence.apply(walk5_cleanParanthesis);
            sentence.apply(walk6_checkNodes);
        }

        /*
         * Finally the syntax tree has to be transformed to an instance
         * of PrologProgram. Therefore the nodes have to be transformed
         * and the directives must be separated from the other clauses.
         */
        final ArrayList<SentenceNode> toDel = new ArrayList<SentenceNode>();
        boolean foundDirective = false, nonEndDirective = false;
        final Set<String> funcNames = new LinkedHashSet<String>(PrologBuiltins.BUILTIN_PREDICATE_NAMES);
        for (final SentenceNode sentence : sentences) {
            final PrologDirective d = PrologParser.toDirective(sentence);
            if (d != null) {
                foundDirective = true;
                directives.add(d);
                toDel.add(sentence);
            } else {
                if (foundDirective) {
                    nonEndDirective = true;
                }
            }
            // gather used function symbol names for FNG
            final InternalNode node = sentence.getChildren().get(0);
            if ((node.getText().equals("-->") || node.getText().equals(":-"))
                && node.getChildren() != null
                && node.getChildren().size() == 2)
            {
                funcNames.addAll(PrologParser.gatherFunctionSymbolNames(node.getChildren().get(0)));
                funcNames.addAll(PrologParser.gatherFunctionSymbolNames(node.getChildren().get(1)));
            } else if (node instanceof ListNode) {
                for (final InternalNode child : node.getChildren()) {
                    if ((child.getText().equals("-->") || child.getText().equals(":-"))
                        && child.getChildren() != null
                        && child.getChildren().size() == 2)
                    {
                        funcNames.addAll(PrologParser.gatherFunctionSymbolNames(child.getChildren().get(0)));
                        funcNames.addAll(PrologParser.gatherFunctionSymbolNames(child.getChildren().get(1)));
                    } else {
                        funcNames.addAll(PrologParser.gatherFunctionSymbolNames(child));
                    }
                }
            } else {
                funcNames.addAll(PrologParser.gatherFunctionSymbolNames(node));
            }
        }
        final FreshNameGenerator fng = new FreshNameGenerator(funcNames, FreshNameGenerator.PROLOG_FUNCS);
        final String append = fng.getFreshName("append", false);
        if (nonEndDirective) { //TODO re-think this convention
            PrologParser.logger.log(Level.WARNING, "Found directives before the end of the program. They will be"
                + " treated as if they occured at the end of the program.");
        }
        sentences.removeAll(toDel);
        //        // Some directives may be queries
        //        final List<PrologDirective> toDelDirectives = new ArrayList<PrologDirective>();
        //        for (final PrologDirective d : directives) {
        //            final List<PrologQuery> queryList = d.toQueries();
        //            if (!queryList.isEmpty()) {
        //                toDelDirectives.add(d);
        //                program.addInternalQueries(queryList);
        //            }
        //        }
        //        directives.removeAll(toDelDirectives);
        final List<PrologClause> clauses = program.getClauses();
        final Notifier note = new Notifier();
        note.used = false;
        for (final SentenceNode sentence : sentences) {
            final InternalNode node = sentence.getChildren().get(0);
            if (node instanceof ListNode
                || (node.getText().equals(PrologBuiltin.LIST_CONSTRUCTOR_NAME) && node.getChildren() != null && node
                    .getChildren()
                    .size() == 2))
            {
                clauses.addAll(PrologParser.toPrologClauses(node, append, note));
            } else {
                clauses.add(PrologParser.toPrologClause(node, append, note));
            }
        }
        if (note.used) {
            // there have been grammar rules using append
            // thus, we add clauses for append
            final List<PrologTerm> args1 = new ArrayList<PrologTerm>();
            final List<PrologTerm> args2 = new ArrayList<PrologTerm>();
            final List<PrologTerm> args3 = new ArrayList<PrologTerm>();
            args1.add(PrologTerms.createEmptyList());
            args1.add(new PrologNonAbstractVariable("YS"));
            args1.add(new PrologNonAbstractVariable("YS"));
            args2.add(PrologTerms.createList(new PrologNonAbstractVariable("X"), new PrologNonAbstractVariable("XS")));
            args2.add(new PrologNonAbstractVariable("YS"));
            args2.add(PrologTerms.createList(new PrologNonAbstractVariable("X"), new PrologNonAbstractVariable("ZS")));
            args3.add(new PrologNonAbstractVariable("XS"));
            args3.add(new PrologNonAbstractVariable("YS"));
            args3.add(new PrologNonAbstractVariable("ZS"));
            clauses.add(new PrologClause(new PrologTerm(append, args1), null));
            clauses.add(new PrologClause(new PrologTerm(append, args2), new PrologTerm(append, args3)));
        }
        // transform underscores
        final Set<String> used = program.getVariableNames();
        used.add("X");
        final FreshNameGenerator fridge = new FreshNameGenerator(used, FreshNameGenerator.PROLOG_VARS);
        program.walkAll(new ReplacementWalker() {

            @Override
            public boolean goDeeper(final PrologTerm term) {
                return true;
            }

            @Override
            public boolean isApplicable(final PrologTerm term) {
                return term != null && term.isNonAbstractVariable() && term.getName().equals("_");
            }

            @Override
            public PrologTerm replace(final PrologTerm term) {
                return term.replaceName(fridge.getFreshName("X", false));
            }

        });
        return program;
    }

    private static ArrayList<PrologClause> toPrologClauses(
        final InternalNode node,
        final String append,
        final Notifier note)
    {
        final ArrayList<PrologClause> res = new ArrayList<PrologClause>();
        final int size = node.getChildren().size();
        for (int i = 0; i < size - 1; i++) {
            final InternalNode child = node.getChildren().get(i);
            if (child instanceof ListNode
                || (child.getText().equals(PrologBuiltin.LIST_CONSTRUCTOR_NAME) && child.getChildren() != null && child
                    .getChildren()
                    .size() == 2))
            {
                res.addAll(PrologParser.toPrologClauses(child, append, note));
            } else {
                res.add(PrologParser.toPrologClause(child, append, note));
            }
        }
        final InternalNode tail = node.getChildren().get(size - 1);
        if (tail instanceof ListNode
            || (tail.getText().equals(PrologBuiltin.LIST_CONSTRUCTOR_NAME) && tail.getChildren() != null && tail
                .getChildren()
                .size() == 2))
        {
            res.addAll(PrologParser.toPrologClauses(tail, append, note));
        } else if (!(tail instanceof VarNode)) {
            res.add(PrologParser.toPrologClause(tail, append, note));
        } // do nothing in case of a variable tail (partial list)
        return res;
    }

    /**
     * Returns a PrologTerm transformed out ouf the specified node of
     * the syntax tree (and so out of a partial tree) concerning the
     * syntactical rules for building a body term in Prolog.
     * @param node The syntax tree node to transform.
     * @return The transformed body PrologTerm.
     */
    private static PrologTerm toBody(final InternalNode node) {
        return PrologParser.toPrologTerm(node); //TODO modules?
    }

    /**
     * Returns a PrologTerm transformed out ouf the specified node of
     * the syntax tree (and so out of a partial tree) concerning the
     * syntactical rules for building a body term in a grammar condition
     * in Prolog.
     * @param node The syntax tree node to transform.
     * @param fridge
     * @param fridge2
     * @param append
     * @param output
     * @param input
     * @param note
     * @return The transformed grammar condition body PrologTerm.
     */
    private static PrologTerm toConditionBody(
        final InternalNode headNode,
        final InternalNode bodyNode,
        final PrologVariable input,
        final PrologVariable output,
        final String append,
        final FreshNameGenerator fridge,
        final Notifier note)
    {
        if (bodyNode == null) {
            if (headNode instanceof TermNode
                && headNode.getText().equals("','")
                && headNode.getChildren() != null
                && headNode.getChildren().size() == 2)
            {
                return PrologParser.grammarTransformation(
                    PrologParser.toHeadTail(headNode),
                    input,
                    output,
                    append,
                    fridge,
                    note);
            } else {
                return null;
            }
        } else if (headNode instanceof TermNode
            && headNode.getText().equals("','")
            && headNode.getChildren() != null
            && headNode.getChildren().size() == 2)
        {
            final PrologVariable bridge = new PrologNonAbstractVariable(fridge.getFreshName("X", false));
            return PrologTerms.createConjunction(PrologParser.grammarTransformation(
                PrologParser.toPrologTerm(bodyNode),
                input,
                bridge,
                append,
                fridge,
                note), PrologParser.grammarTransformation(
                PrologParser.toHeadTail(headNode),
                output,
                bridge,
                append,
                fridge,
                note));
        } else {
            final PrologTerm bodyTerm = PrologParser.toPrologTerm(bodyNode);
            return PrologParser.grammarTransformation(bodyTerm, input, output, append, fridge, note);
        }
    }

    private static PrologTerm grammarTransformation( //TODO consider cuts!
        final PrologTerm term,
        final PrologVariable input,
        final PrologVariable output,
        final String append,
        final FreshNameGenerator fridge,
        final Notifier note)
    {
        if (term.isDisjunctionTerm()) {
            return PrologTerms.createDisjunction(
                PrologParser.grammarTransformation(term.getArgument(0), input, output, append, fridge, note),
                PrologParser.grammarTransformation(term.getArgument(1), input, output, append, fridge, note));
        } else if (term.isConjunction()) {
            final PrologVariable bridge = new PrologNonAbstractVariable(fridge.getFreshName("X", false));
            return PrologTerms.flattenConjunction(PrologTerms.createConjunction(
                PrologParser.grammarTransformation(term.getArgument(0), input, bridge, append, fridge, note),
                PrologParser.grammarTransformation(term.getArgument(1), bridge, output, append, fridge, note)));
        } else if (term.isIf()) {
            final PrologVariable bridge = new PrologNonAbstractVariable(fridge.getFreshName("X", false));
            final List<PrologTerm> args = new ArrayList<PrologTerm>();
            args.add(PrologParser.grammarTransformation(term.getArgument(0), input, bridge, append, fridge, note));
            args.add(PrologParser.grammarTransformation(term.getArgument(1), bridge, output, append, fridge, note));
            return new PrologTerm(PrologBuiltin.IF_NAME, args);
        } else if (term.isList()) {
            if (term.isFiniteList()) {
                final List<PrologTerm> args = new ArrayList<PrologTerm>();
                args.add(input);
                args.add(PrologTerms.listAppend(term, output));
                return new PrologTerm(PrologBuiltin.UNIFY_NAME, args);
            } else {
                note.used = true;
                final List<PrologTerm> args = new ArrayList<PrologTerm>();
                args.add(term);
                args.add(output);
                args.add(input);
                return new PrologTerm(append, args);
            }
        } else if (term.getName().equals("{}")) {
            final List<PrologTerm> conjuncts = new ArrayList<PrologTerm>(term.getArguments());
            final List<PrologTerm> args = new ArrayList<PrologTerm>();
            args.add(output);
            args.add(input);
            conjuncts.add(new PrologTerm(PrologBuiltin.UNIFY_NAME, args));
            return PrologTerms.createConjunction(conjuncts);
        } else {
            return term.add(input).add(output);
        }
    }

    private static PrologTerm toHeadTail(final InternalNode node) {
        final List<PrologTerm> conjuncts = new ArrayList<PrologTerm>();
        conjuncts.add(PrologParser.toPrologTerm(node.getChildren().get(1)));
        InternalNode headNode = node.getChildren().get(0);
        while (headNode instanceof TermNode
            && headNode.getText().equals("','")
            && headNode.getChildren() != null
            && headNode.getChildren().size() == 2)
        {
            conjuncts.add(PrologParser.toPrologTerm(headNode.getChildren().get(1)));
            headNode = headNode.getChildren().get(0);
        }
        Collections.reverse(conjuncts);
        return PrologTerms.createConjunction(conjuncts);
    }

    private static PrologTerm toConditionHead(
        InternalNode node,
        final List<InternalNode> elements,
        final PrologVariable input,
        final PrologVariable output)
    {
        while (node instanceof TermNode
            && node.getText().equals("','")
            && node.getChildren() != null
            && node.getChildren().size() == 2)
        {
            node = node.getChildren().get(0);
        }
        if (!(node instanceof TermNode)) {
            throw new PrologSyntaxException("Cannot parse grammar rule at ("
                + node.getLine()
                + ", "
                + node.getPos()
                + ")");
        }
        final PrologTerm res = PrologParser.toPrologTerm(node);
        PrologTerm list = input;
        if (elements != null) {
            for (int i = elements.size() - 1; i >= 0; i--) {
                final List<PrologTerm> args = new ArrayList<PrologTerm>();
                args.add(PrologParser.toPrologTerm(elements.get(i)));
                args.add(list);
                list = new PrologTerm(PrologBuiltin.LIST_CONSTRUCTOR_NAME, args);
            }
        }
        return res.add(list).add(output);
    }

    /**
     * Transforms the given SentenceNode to a PrologDirective if the
     * sentence really is a directive. Otherwise this method returns
     * null.
     * @param sentence The sentence to transform.
     * @return The transformed PrologDirective or null if the sentence
     *         is no directive.
     */
    private static PrologDirective toDirective(final SentenceNode sentence) {
        if (PrologParser.isDirective(sentence)) {
            return new PrologDirective(PrologParser.toPrologTerm(sentence.getChildren().get(0).getChildren().get(0)));
        }
        return null;
    }

    /**
     * Returns a PrologTerm transformed out ouf the specified node of
     * the syntax tree (and so out of a partial tree) concerning the
     * syntactical rules for building a head term in Prolog.
     * @param node The syntax tree node to transform.
     * @return The transformed head PrologTerm.
     */
    private static PrologTerm toHead(final InternalNode node) {
        if (!(node instanceof TermNode)) {
            throw new PrologSyntaxException("Illegal head declaration!(" + node.getLine() + ", " + node.getPos() + ")");
        }
        final String name = node.getText();
        final int arity = node.getChildren() == null ? 0 : node.getChildren().size();
        if (name.equals("','") && arity == 2) {
            throw new PrologSyntaxException("','->/2 not allowed to define in head declaration!("
                + node.getLine()
                + ", "
                + node.getPos()
                + ")");
        } else if (name.equals(";") && arity == 2) {
            throw new PrologSyntaxException(";/2 not allowed to define in head declaration!("
                + node.getLine()
                + ", "
                + node.getPos()
                + ")");
        } else if (name.equals("->") && arity == 2) {
            throw new PrologSyntaxException("->/2 not allowed to define in head declaration!("
                + node.getLine()
                + ", "
                + node.getPos()
                + ")");
        } else if (name.equals("\\+") && arity == 1) {
            throw new PrologSyntaxException("\\+/1 not allowed to define in head declaration!("
                + node.getLine()
                + ", "
                + node.getPos()
                + ")");
        }
        return PrologParser.toPrologTerm(node); //TODO modules?
    }

    /**
     * Transforms the given node of the syntax tree (and so the partial
     * syntax tree) to a PrologClause.
     * @param node The node to transform.
     * @param fng
     * @return The transformed PrologClause.
     */
    private static PrologClause toPrologClause(final InternalNode node, final String append, final Notifier note) { //TODO modules?
        if (node.getText().equals("-->") && node.getChildren() != null && node.getChildren().size() == 2) {
            return PrologParser.transformGrammarRuleToClause(
                node.getChildren().get(0),
                node.getChildren().get(1),
                append,
                note);
        } else if (node.getText().equals(":-") && node.getChildren() != null && node.getChildren().size() == 2) {
            return new PrologClause(PrologParser.toHead(node.getChildren().get(0)), PrologParser.toBody(node
                .getChildren()
                .get(1)));
        } else if (node instanceof ListNode) {
            throw new IllegalArgumentException("This method only accepts single clauses!");
        } else {
            return new PrologClause(PrologParser.toHead(node), null);
        }
    }

    /**
     * Returns a PrologTerm transformed out ouf the specified node of
     * the syntax tree (and so out of a partial tree) concerning the
     * syntactical rules for building a term in Prolog.
     * @param node The syntax tree node to transform.
     * @return The transformed PrologTerm.
     */
    private static PrologTerm toPrologTerm(final InternalNode node) {
        PrologTerm res = null;
        if (node instanceof TermNode) {
            if (node.getChildren() == null) {
                res = new PrologTerm(node.getText());
            } else {
                res = new PrologTerm(node.getText(), PrologParser.toPrologTerms(node.getChildren()));
            }
        } else if (node instanceof VarNode) {
            res = new PrologNonAbstractVariable(node.getText());
        } else if (node instanceof EmptyListNode) {
            res = new PrologTerm("[]");
        } else if (node instanceof CutNode) {
            res = new PrologTerm("!");
        } else if (node instanceof IntNode) {
            res = new PrologInt(node.getText());
        } else if (node instanceof FloatNode) {
            res = new PrologFloat(node.getText());
        } else if (node instanceof StringNode) {
            final List<PrologTerm> list = new ArrayList<PrologTerm>();
            final byte[] bytes = node.getText().getBytes();
            for (int i = 1; i < bytes.length - 1; i++) {
                // convert signed bytes to unsigned integers
                list.add(new PrologInt(BigInteger.valueOf(bytes[i] & 0xFF)));
            }
            res = PrologTerms.createList(list);
        } else if (node instanceof InfNode || node instanceof NanNode) {
            res = new PrologNumber(node.getText());
        } else if (node instanceof ConditionNode) {
            // a grammar condition is used outside a grammar rule
            // thus, it is parsed as a term according to SWI
            if (node.getChildren() == null) {
                res = new PrologTerm("{}");
            } else {
                res = new PrologTerm("{}", PrologParser.toPrologTerms(node.getChildren()));
            }
        } else {
            throw new PrologSyntaxException("Unexpected term occured!(" + node.getLine() + ", " + node.getPos() + ")");
        }
        return res;
    }

    /**
     * Returns an ArrayList of PrologTerms transformed out ouf the
     * specified nodes of the syntax tree (and so out of a partial trees)
     * concerning the syntactical rules for building terms in Prolog.
     * @param nodes The syntax tree nodes to transform.
     * @return The transformed PrologTerms.
     */
    private static List<PrologTerm> toPrologTerms(final List<InternalNode> nodes) {
        final ArrayList<PrologTerm> res = new ArrayList<PrologTerm>();
        if (nodes != null) {
            for (final InternalNode node : nodes) {
                res.add(PrologParser.toPrologTerm(node));
            }
        }
        return res;
    }

    private static PrologClause transformGrammarRuleToClause(
        final InternalNode headNode,
        final InternalNode bodyNode,
        final String append,
        final Notifier note)
    {
        final List<String> used = PrologParser.extractVariableNames(headNode);
        used.addAll(PrologParser.extractVariableNames(bodyNode));
        used.add("X");
        final FreshNameGenerator fridge = new FreshNameGenerator(used, FreshNameGenerator.PROLOG_VARS);
        final PrologVariable input = new PrologNonAbstractVariable(fridge.getFreshName("X", false));
        final PrologVariable output = new PrologNonAbstractVariable(fridge.getFreshName("X", false));
        if (bodyNode instanceof ListNode
            || bodyNode instanceof EmptyListNode
            || bodyNode instanceof StringNode
            || (bodyNode.getText().equals(PrologBuiltin.LIST_CONSTRUCTOR_NAME) && bodyNode.getChildren() != null && bodyNode
                .getChildren()
                .size() == 2))
        {
            if (bodyNode instanceof ListNode
                || (bodyNode.getText().equals(PrologBuiltin.LIST_CONSTRUCTOR_NAME) && bodyNode.getChildren() != null && bodyNode
                    .getChildren()
                    .size() == 2))
            {
                InternalNode tail = bodyNode.getChildren().get(bodyNode.getChildren().size() - 1);
                while (tail instanceof ListNode
                    || (tail.getText().equals(PrologBuiltin.LIST_CONSTRUCTOR_NAME) && tail.getChildren() != null && tail
                        .getChildren()
                        .size() == 2))
                {
                    tail = tail.getChildren().get(tail.getChildren().size() - 1);
                }
                if (!(tail instanceof VarNode)) {
                    return new PrologClause(PrologParser.toConditionHead(
                        headNode,
                        PrologParser.getFlattenedListElements(bodyNode),
                        input,
                        output), PrologParser.toConditionBody(headNode, null, input, output, append, fridge, note));
                }
                // in case of a partial list, we reach
                // the last return statement (general case)
            } else {
                return new PrologClause(
                    PrologParser.toConditionHead(headNode, bodyNode.getChildren(), input, output),
                    PrologParser.toConditionBody(headNode, null, input, output, append, fridge, note));
            }
        }
        return new PrologClause(
            PrologParser.toConditionHead(headNode, new ArrayList<InternalNode>(), input, output),
            PrologParser.toConditionBody(headNode, bodyNode, input, output, append, fridge, note));
    }

    private static List<InternalNode> getFlattenedListElements(final InternalNode node) {
        final List<InternalNode> res = new ArrayList<InternalNode>();
        if (node.getChildren() != null) {
            for (final InternalNode child : node.getChildren()) {
                if (child instanceof ListNode
                    || (child.getText().equals(PrologBuiltin.LIST_CONSTRUCTOR_NAME) && child.getChildren() != null && child
                        .getChildren()
                        .size() == 2))
                {
                    res.addAll(PrologParser.getFlattenedListElements(child));
                } else {
                    res.add(child);
                }
            }
        }
        return res;
    }

    private PrologParser() {
        // no object
    }

    private static class NonOpWalker implements TreeWalker {

        private final PrologOperatorSet ops;

        private NonOpWalker(final PrologOperatorSet ops) {
            this.ops = ops;
        }

        @Override
        public void action(final InternalNode node) {
            final List<InternalNode> children = node.getChildren();
            if (children != null) {
                // to extract all name tokens
                final ArrayList<NameNode> names = new ArrayList<NameNode>();
                // to extract all list tokens (nonempty lists)
                final ArrayList<EmptyListNode> lists = new ArrayList<EmptyListNode>();
                // to extract all cut tokens
                final ArrayList<CutNode> cuts = new ArrayList<CutNode>();

                // extract the three kinds of tokens
                for (final InternalNode child : children) {
                    if (child instanceof NameNode) {
                        names.add((NameNode) child);
                    } else if (child instanceof EmptyListNode) {
                        lists.add((EmptyListNode) child);
                    } else if (child instanceof CutNode) {
                        cuts.add((CutNode) child);
                    }
                }

                // this TreeWalker handles only those name tokens that can
                // not be seen as operators anyway
                final ArrayList<NameNode> toDel = new ArrayList<NameNode>();
                for (final NameNode name : names) {
                    if (this.ops.isOperator(name.getText())) {
                        toDel.add(name);
                    }
                }
                names.removeAll(toDel);

                // build constant or compound terms out of name tokens
                for (final NameNode name : names) {
                    final int index = children.indexOf(name);
                    if (children.size() > index + 1) {
                        final InternalNode next = children.get(index + 1); // the following token
                        if (next instanceof ParanthesisNode) {
                            // it's a compound term
                            final TermNode term = new TermNode(name.getText(), 0, name.getLine(), name.getPos());
                            final List<InternalNode> nodes = next.getChildren();
                            //TODO check whether null can occur here
                            for (final InternalNode n : nodes) {
                                term.addChild(n);
                            }
                            children.remove(next);
                            children.set(index, term);
                            continue; // see the next name
                        } else if ((next instanceof IntNode || next instanceof FloatNode || next instanceof NanNode || next instanceof InfNode)
                            && !next.getText().startsWith("+")
                            && !next.getText().startsWith("-"))
                        { // maybe it belongs to a number
                            final String opName = name.getText();
                            if (opName.equals("+") || opName.equals("-")) {
                                // it's the sign of a number
                                if (next instanceof IntNode) {
                                    final IntNode newNode =
                                        new IntNode(opName + next.getText(), name.getLine(), name.getPos());
                                    children.remove(next);
                                    children.set(index, newNode);
                                } else if (next instanceof FloatNode) {
                                    final FloatNode newNode =
                                        new FloatNode(opName + next.getText(), name.getLine(), name.getPos());
                                    children.remove(next);
                                    children.set(index, newNode);
                                } else if (next instanceof NanNode) {
                                    final NanNode newNode =
                                        new NanNode(opName + next.getText(), name.getLine(), name.getPos());
                                    children.remove(next);
                                    children.set(index, newNode);
                                } else {
                                    final InfNode newNode =
                                        new InfNode(opName + next.getText(), name.getLine(), name.getPos());
                                    children.remove(next);
                                    children.set(index, newNode);
                                }
                                continue; // see the next name
                            }
                        }
                    }
                    // otherwise it's a constant
                    children.set(index, new TermNode(name.getText(), 0, name.getLine(), name.getPos()));
                }
                // [] can be a name and therefore the functor of a compound term
                if (!this.ops.isOperator("[]")) {
                    for (final EmptyListNode l : lists) {
                        final int index = children.indexOf(l);
                        if (index + 1 < children.size()) {
                            final InternalNode next = children.get(index + 1);
                            if (next instanceof ParanthesisNode) {
                                final TermNode term = new TermNode("[]", 0, l.getLine(), l.getPos());
                                //TODO check whether null can occur here
                                for (final InternalNode n : next.getChildren()) {
                                    term.addChild(n);
                                }
                                children.remove(next);
                                children.set(index, term);
                            }
                        }
                    }
                }
                // ! can be a name and therefore the functor of a compound term
                if (!this.ops.isOperator("!")) {
                    for (final CutNode cut : cuts) {
                        final int index = children.indexOf(cut);
                        if (index + 1 < children.size()) {
                            final InternalNode next = children.get(index + 1);
                            if (next instanceof ParanthesisNode) {
                                final TermNode term = new TermNode("!", 0, cut.getLine(), cut.getPos());
                                //TODO check whether null can occur here
                                for (final InternalNode n : next.getChildren()) {
                                    term.addChild(n);
                                }
                                children.remove(next);
                                children.set(index, term);
                            }
                        }
                    }
                }
            }
        }

    }

    private static class OpWalker implements TreeWalker {

        private final PrologOperatorSet ops;

        private OpWalker(final PrologOperatorSet ops) {
            this.ops = ops;
        }

        @Override
        public void action(final InternalNode node) {
            final List<InternalNode> children = node.getChildren();
            if (children != null) {
                new PrologTermBuilder(children, this.ops).build();
            }
        }

    }

    private static class CleanLayoutWalker implements TreeWalker {

        @Override
        public void action(final InternalNode node) {
            final List<InternalNode> children = node.getChildren();
            if (children != null) {
                final ArrayList<InternalNode> toDel = new ArrayList<InternalNode>();
                for (final InternalNode child : children) {
                    if (child instanceof LayoutNode) {
                        toDel.add(child);
                    }
                }
                children.removeAll(toDel);
            }
        }

    }

    private static class CleanCommaListWalker implements TreeWalker {

        @Override
        public void action(final InternalNode node) {
            final List<InternalNode> children = node.getChildren();
            if (children != null) {

                /*
                 * As commas can be separators in lists on the one hand or infix
                 * operators which cannot be redefined in a paranthesis, a
                 * grammar condition in curly brackets and in the argument list
                 * of a functor on the other hand they must be handled in a
                 * special way. The seperators can just be removed and the
                 * separated tokens are the several items of the certain list.
                 * The operators, however, are in Prolog seen as terms with the
                 * functor "','" instead of ",". So the operator terms have to
                 * be replaced with that new functor. Similarly lists are seen
                 * as terms with the functor ".". So the lists have to be
                 * replaced by those terms, too. By cleaning the commas and
                 * lists, some syntax errors like missing arguments before or
                 * after commas or pipes and an empty paranthesis are detected
                 * and in case of detection a PrologSyntaxException is thrown.
                 */
                final ArrayList<ParanthesisNode> paranthesis = new ArrayList<ParanthesisNode>();
                final ArrayList<ListNode> lists = new ArrayList<ListNode>();
                final ArrayList<ConditionNode> conditions = new ArrayList<ConditionNode>();
                final ArrayList<TermNode> terms = new ArrayList<TermNode>();
                for (final InternalNode child : children) {
                    if (child instanceof ParanthesisNode) {
                        paranthesis.add((ParanthesisNode) child);
                    } else if (child instanceof ListNode) {
                        lists.add((ListNode) child);
                    } else if (child instanceof ConditionNode) {
                        conditions.add((ConditionNode) child);
                    } else if (child instanceof TermNode) {
                        terms.add((TermNode) child);
                    }
                }
                for (final ParanthesisNode p : paranthesis) {
                    final List<InternalNode> nodes = p.getChildren();
                    if (nodes == null || nodes.isEmpty()) {
                        throw new PrologSyntaxException("Empty paranthesis occured!("
                            + p.getLine()
                            + ", "
                            + p.getPos()
                            + ")");
                    }
                    final int index = children.indexOf(p);
                    if (nodes.get(0) instanceof CommaNode) {
                        throw new PrologSyntaxException("There is no argument before the first comma!("
                            + nodes.get(0).getLine()
                            + ", "
                            + nodes.get(0).getPos()
                            + ")");
                    }
                    if (nodes.size() == 1) {
                        continue; // next paranthesis
                    }
                    final int precedence = p instanceof OpParanthesisNode ? 1000 : 0;
                    final TermNode term =
                        new TermNode("','", precedence, nodes.get(1).getLine(), nodes.get(1).getPos());
                    TermNode comma = term;
                    for (int akt = 0; akt < nodes.size(); akt++) {
                        InternalNode n = nodes.get(akt);
                        if (n instanceof CommaNode) {
                            final CommaNode comNode = (CommaNode) n;
                            akt++;
                            if (akt == nodes.size()) {
                                throw new PrologSyntaxException("There is no argument after the last"
                                    + " comma!("
                                    + comNode.getLine()
                                    + ", "
                                    + comNode.getPos()
                                    + ")");
                            }
                            n = nodes.get(akt);
                            if (n instanceof CommaNode) {
                                throw new PrologSyntaxException("There is no argument between two"
                                    + " commas!("
                                    + n.getLine()
                                    + ", "
                                    + n.getPos()
                                    + ")");
                            }
                            if (akt != nodes.size() - 1) {
                                final TermNode newComma =
                                    new TermNode("','", precedence, comNode.getLine(), comNode.getPos());
                                comma.addChild(newComma);
                                if (comma.getChildren().size() > 2) {
                                    throw new PrologSyntaxException("There are two arguments without an"
                                        + " operator or separator!("
                                        + comma.getChildren().get(0).getLine()
                                        + ", "
                                        + comma.getChildren().get(0).getPos()
                                        + ")");
                                }
                                comma = newComma;
                            }
                        }
                        comma.addChild(n);
                        if (comma.getChildren().size() > 2) {
                            throw new PrologSyntaxException("There are two arguments without an operator"
                                + " or separator!("
                                + comma.getChildren().get(0).getLine()
                                + ", "
                                + comma.getChildren().get(0).getPos()
                                + ")");
                        }
                    }
                    children.set(index, term);
                }
                for (final ListNode l : lists) {
                    final int index = children.indexOf(l);
                    final List<InternalNode> nodes = l.getChildren();
                    if (nodes == null || nodes.isEmpty()) {
                        throw new IllegalStateException("The elements of a nonempty list have been erased!");
                    }
                    if (nodes.size() == 1) {
                        final TermNode t =
                            new TermNode(PrologBuiltin.LIST_CONSTRUCTOR_NAME, 0, l.getLine(), l.getPos());
                        t.addChild(nodes.get(0));
                        t.addChild(new EmptyListNode(l.getLine(), l.getPos()));
                        children.set(index, t);
                        continue; // next list
                    }
                    final ArrayList<TermNode> args = new ArrayList<TermNode>();
                    for (int i = 0; i < nodes.size(); i++) {
                        final InternalNode akt = nodes.get(i);
                        InternalNode next = null;
                        final TermNode t =
                            new TermNode(PrologBuiltin.LIST_CONSTRUCTOR_NAME, 0, l.getLine(), l.getPos());
                        if (akt instanceof CommaNode || akt instanceof PunctuationNode) {
                            throw new PrologSyntaxException("Unexpected punctuation token in list!("
                                + akt.getLine()
                                + ", "
                                + akt.getPos()
                                + ")");
                        }
                        if (i + 1 < nodes.size()) {
                            next = nodes.get(i + 1);
                            if (next instanceof PunctuationNode && next.getText().equals("|")) {
                                if (i + 3 == nodes.size()) {
                                    final InternalNode last = nodes.get(i + 2);
                                    if (last instanceof CommaNode || last instanceof PunctuationNode) {
                                        throw new PrologSyntaxException("Unexpected element at end of"
                                            + " list!("
                                            + last.getLine()
                                            + ", "
                                            + last.getPos()
                                            + ")");
                                    }
                                    t.addChild(akt);
                                    t.addChild(last);
                                    args.add(t);
                                    break;
                                } else {
                                    throw new PrologSyntaxException("Unexpected number of elements after"
                                        + " pipe!("
                                        + next.getLine()
                                        + ", "
                                        + next.getPos()
                                        + ")");
                                }
                            } else if (next instanceof CommaNode) {
                                i++;
                                t.addChild(akt);
                            } else {
                                throw new PrologSyntaxException("Two elements in the list are not"
                                    + " seperated by a comma or pipe!("
                                    + next.getLine()
                                    + ", "
                                    + next.getPos()
                                    + ")");
                            }
                        } else {
                            t.addChild(akt);
                            t.addChild(new EmptyListNode(l.getLine(), l.getPos()));
                        }
                        args.add(t);
                    }
                    for (int i = 0; i < args.size() - 1; i++) {
                        if (args.get(i + 1) == null) {
                            break;
                        }
                        args.get(i).addChild(args.get(i + 1));
                    }
                    children.set(index, args.get(0));
                }
                for (final ConditionNode c : conditions) {
                    final List<InternalNode> nodes = c.getChildren();
                    if (nodes == null || nodes.isEmpty()) {
                        throw new PrologSyntaxException("Empty grammar condition occured!("
                            + c.getLine()
                            + ", "
                            + c.getPos()
                            + ")");
                    }
                    final ArrayList<InternalNode> commas = new ArrayList<InternalNode>();
                    if (nodes.get(0) instanceof CommaNode) {
                        throw new PrologSyntaxException("There is no argument before the first comma!("
                            + nodes.get(0).getLine()
                            + ", "
                            + nodes.get(0).getPos()
                            + ")");
                    }
                    if (nodes.get(nodes.size() - 1) instanceof CommaNode) {
                        throw new PrologSyntaxException("There is no argument after the last comma!("
                            + nodes.get(nodes.size() - 1).getLine()
                            + ", "
                            + nodes.get(nodes.size() - 1).getPos()
                            + ")");
                    }
                    if (nodes.size() == 1) {
                        continue; // next grammar condition
                    }
                    for (int akt = 0; akt < nodes.size(); akt++) {
                        final InternalNode n = nodes.get(akt);
                        if (n instanceof CommaNode) {
                            commas.add(n);
                            akt++;
                            if (akt < nodes.size() && nodes.get(akt) instanceof CommaNode) {
                                throw new PrologSyntaxException("There is no argument between two"
                                    + " commas!("
                                    + n.getLine()
                                    + ", "
                                    + n.getPos()
                                    + ")");
                            }
                        } else if (akt + 1 < nodes.size() && !(nodes.get(akt + 1) instanceof CommaNode)) {
                            throw new PrologSyntaxException("There are two arguments without an operator"
                                + " or separator!("
                                + n.getLine()
                                + ", "
                                + n.getPos()
                                + ")");
                        }
                    }
                    nodes.removeAll(commas);
                }
                for (final TermNode t : terms) {
                    if (t.getPrecedence() == 0) {
                        final List<InternalNode> nodes = t.getChildren();
                        if (nodes == null) {
                            throw new NullPointerException("A term's children list has been erased!");
                        }
                        if (!nodes.isEmpty()) {
                            final ArrayList<InternalNode> commas = new ArrayList<InternalNode>();
                            if (nodes.get(0) instanceof CommaNode) {
                                throw new PrologSyntaxException("There is no argument before the first"
                                    + " comma!("
                                    + nodes.get(0).getLine()
                                    + ", "
                                    + nodes.get(0).getPos()
                                    + ")");
                            }
                            if (nodes.get(nodes.size() - 1) instanceof CommaNode) {
                                throw new PrologSyntaxException("There is no argument after the last"
                                    + " comma!("
                                    + nodes.get(nodes.size() - 1).getLine()
                                    + ", "
                                    + nodes.get(nodes.size() - 1).getPos()
                                    + ")");
                            }
                            for (int akt = 0; akt < nodes.size(); akt++) {
                                final InternalNode n = nodes.get(akt);
                                if (n instanceof CommaNode) {
                                    commas.add(n);
                                    akt++;
                                    if (akt < nodes.size() && (nodes.get(akt) instanceof CommaNode)) {
                                        throw new PrologSyntaxException("There is no argument between two"
                                            + " commas!("
                                            + n.getLine()
                                            + ", "
                                            + n.getPos()
                                            + ")");
                                    }
                                } else if (akt + 1 < nodes.size() && !(nodes.get(akt + 1) instanceof CommaNode)) {
                                    throw new PrologSyntaxException("There are two arguments without an"
                                        + " operator or separator!("
                                        + n.getLine()
                                        + ", "
                                        + n.getPos()
                                        + ")");
                                }
                            }
                            nodes.removeAll(commas);
                        }
                    } else if (t.getPrecedence() >= 1000) {
                        final List<InternalNode> nodes = t.getChildren();
                        if (nodes == null) {
                            throw new NullPointerException("A term's children list has been erased!");
                        }
                        if (nodes.isEmpty()) {
                            throw new PrologSyntaxException("Operator without argument occured!("
                                + t.getLine()
                                + ", "
                                + t.getPos()
                                + ")");
                        }
                        if (nodes.get(0) instanceof CommaNode) {
                            throw new PrologSyntaxException("There is no argument before the first"
                                + " comma!("
                                + nodes.get(0).getLine()
                                + ", "
                                + nodes.get(0).getPos()
                                + ")");
                        }
                        if (nodes.get(nodes.size() - 1) instanceof CommaNode) {
                            throw new PrologSyntaxException("There is no argument after the last comma!("
                                + nodes.get(nodes.size() - 1).getLine()
                                + ", "
                                + nodes.get(nodes.size() - 1).getPos()
                                + ")");
                        }
                        if (nodes.size() == 1 || nodes.size() == 2) {
                            continue;
                        }
                        final TermNode term = new TermNode("','", 1000, nodes.get(1).getLine(), nodes.get(1).getPos());
                        TermNode comma = term;
                        for (int akt = 0; akt < nodes.size(); akt++) {
                            InternalNode n = nodes.get(akt);
                            if (n instanceof CommaNode) {
                                final CommaNode comNode = (CommaNode) n;
                                akt++;
                                n = nodes.get(akt);
                                if (n instanceof CommaNode) {
                                    throw new PrologSyntaxException("There is no argument between two"
                                        + " commas!("
                                        + comNode.getLine()
                                        + ", "
                                        + comNode.getPos()
                                        + ")");
                                }
                                if (akt != nodes.size() - 1) {
                                    final TermNode newComma =
                                        new TermNode("','", 1000, comNode.getLine(), comNode.getPos());
                                    comma.addChild(newComma);
                                    if (comma.getChildren().size() > 2) {
                                        throw new PrologSyntaxException("There are two arguments without"
                                            + " an operator or separator!("
                                            + (comma.getChildren().get(0).getLine())
                                            + ", "
                                            + (comma.getChildren().get(0).getPos())
                                            + ")");
                                    }
                                    comma = newComma;
                                }
                            }
                            comma.addChild(n);
                            if (comma.getChildren().size() > 2) {
                                throw new PrologSyntaxException("There are two arguments without an"
                                    + " operator or separator!("
                                    + comma.getChildren().get(0).getLine()
                                    + ", "
                                    + comma.getChildren().get(0).getPos()
                                    + ")");
                            }
                        }
                        nodes.clear();
                        nodes.add(term);
                    }
                }
            }
        }

    }

    private static class CleanParanthesisWalker implements TreeWalker {

        @Override
        public void action(final InternalNode node) {
            final List<InternalNode> children = node.getChildren();
            if (children != null) {
                final ArrayList<ParanthesisNode> paranthesis = new ArrayList<ParanthesisNode>();
                for (final InternalNode child : children) {
                    if (child instanceof ParanthesisNode) {
                        paranthesis.add((ParanthesisNode) child);
                    }
                }
                if (node instanceof TermNode
                    && ((TermNode) node).getPrecedence() == 0
                    && !(node.getText().equals(PrologBuiltin.LIST_CONSTRUCTOR_NAME) && children.size() == 2))
                {
                    for (final InternalNode child : children) {
                        if (child instanceof TermNode) {
                            if (((TermNode) child).getPrecedence() >= 1000) {
                                throw new PrologSyntaxException("The arguments of a compound term must"
                                    + " have a precedence below 1000!("
                                    + child.getLine()
                                    + ", "
                                    + child.getPos()
                                    + ")");
                            }
                        }
                    }
                }
                for (final ParanthesisNode p : paranthesis) {
                    final int index = children.indexOf(p);
                    final List<InternalNode> nodes = p.getChildren();
                    if (nodes == null || nodes.size() != 1) {
                        throw new PrologSyntaxException("Unexpected number of arguments!("
                            + p.getLine()
                            + ", "
                            + p.getPos()
                            + ")");
                    }
                    final InternalNode child = nodes.get(0);
                    if (child instanceof TermNode) {
                        ((TermNode) child).paranthesised();
                    }
                    children.set(index, child);
                }
            }
        }

    }

    private static class CheckWalker implements TreeWalker {

        @Override
        public void action(final InternalNode node) {
            if (node instanceof NameNode) {
                throw new PrologSyntaxException("Unable to handle "
                    + node.getText()
                    + " token!("
                    + node.getLine()
                    + ", "
                    + node.getPos()
                    + ")");
            } else if (node instanceof ParanthesisNode) {
                throw new PrologSyntaxException("Could not remove every paranthesis!("
                    + node.getLine()
                    + ", "
                    + node.getPos()
                    + ")");
            } else if (node instanceof CommaNode) {
                throw new PrologSyntaxException("Could not handle all commas!("
                    + node.getLine()
                    + ", "
                    + node.getPos()
                    + ")");
            } else if (node instanceof SentenceNode) {
                final List<InternalNode> children = node.getChildren();
                if (children == null || children.isEmpty()) {
                    throw new PrologSyntaxException("Empty sentence occured!("
                        + node.getLine()
                        + ", "
                        + node.getPos()
                        + ")");
                }
                if (children.size() > 1) {
                    throw new PrologSyntaxException("Could not handle all tokens in this sentence!("
                        + node.getLine()
                        + ", "
                        + node.getPos()
                        + ")");
                }
                PrologParser.checkSentence(children.get(0));
            } else if (node instanceof TermNode) {
                final List<InternalNode> children = node.getChildren();
                if (children == null) {
                    throw new NullPointerException("A term's children list has been erased!");
                }
                if (((TermNode) node).getPrecedence() > 0) {
                    if (children.isEmpty()) {
                        throw new PrologSyntaxException("An operator without argument occured!("
                            + node.getLine()
                            + ", "
                            + node.getPos()
                            + ")");
                    }
                }
            }
        }

    }

    private static class Notifier {

        private boolean used;

    }

}
