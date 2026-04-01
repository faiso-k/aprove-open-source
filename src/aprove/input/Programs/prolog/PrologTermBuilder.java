package aprove.input.Programs.prolog;

import java.util.*;

import aprove.input.Programs.prolog.nodes.*;

/**
 * Control class for building terms in Prolog out of a token list.
 * The PrologTermBuilder expects the token list to be prepared in the way
 * that all names that are not declared as operators anyway are built to
 * terms already and that layout text has not been cleaned from the token
 * list yet. So it is not a real token list anymore but for the
 * PrologTermBuilder all prebuilt terms are handled just like tokens.
 * The PrologTermBuilder will affect the token list directly and will
 * change it to a kind of syntax tree which is not completely finished,
 * but which contains no name tokens anymore, except commas. Further
 * operations have to clean the layout text, paranthesis tokens and
 * commas and check the syntax tree for correctness.<br><br>
 *
 * Created: 01.06.2006<br>
 * Last modified: 11.07.2006
 *
 * @author cryingshadow
 * @version $Id$
 */
public class PrologTermBuilder {

    private Comparator<OpNode> comp;
    private PrologOperatorSet[] fixSets;
    private ArrayList<OpNode> infixOps,
                              postfixOps,
                              prefixOps;
    private PrologOperatorSet set;
    private List<InternalNode> tokens;

//------------------------ constructors ------------------------

    /**
     * The constructor expects the token list and a set of operator
     * declarations. The specified token list will directly be changed
     * by invoking the build() method.
     * @param toks The token list.
     * @param ops The operator declarations.
     */
    public PrologTermBuilder (List<InternalNode> toks, PrologOperatorSet ops) {
        this.tokens = toks;
        this.prefixOps = new ArrayList<OpNode>();
        this.infixOps = new ArrayList<OpNode>();
        this.postfixOps = new ArrayList<OpNode>();
        this.set = ops;
        /*
         * The following comparator defines a totally order on the
         * possible operators in the token list.
         * Operators with higher precedence are smaller than other ones.
         * If two operators have the same precedence, then the fixity
         * decides which one is the bigger one. Prefix operators are
         * smaller than infix operators and the latter ones are
         * smaller than postfix operators. If two operators have the
         * same precedence and fixity their position will decide their
         * order. The leftmost prefix or infix operator (except right
         * associative ones) is the smallest one as is the rightmost
         * postfix operator (or right associative infix operator).
         */
        this.comp = new Comparator<OpNode>() {
            @Override
            public int compare (OpNode n1, OpNode n2) {
                if (n1.precedence == n2.precedence) {
                    switch (n1.fixity) {
                        case PrologOperatorSet.FX:
                        case PrologOperatorSet.FY:
                            if (n2.fixity == PrologOperatorSet.XFX || n2.fixity == PrologOperatorSet.YFX || n2.fixity == PrologOperatorSet.XFY || n2.fixity == PrologOperatorSet.YF || n2.fixity == PrologOperatorSet.XF) {
                                return -1;
                            }
                            return PrologTermBuilder.this.tokens.indexOf(n1.name) - PrologTermBuilder.this.tokens.indexOf(n2.name);
                        case PrologOperatorSet.XFY:
                            if (n2.fixity == PrologOperatorSet.XFX || n2.fixity == PrologOperatorSet.YFX) {
                                return 1;
                            }
                            if (n2.fixity == PrologOperatorSet.XFY) {
                                return PrologTermBuilder.this.tokens.indexOf(n2.name) - PrologTermBuilder.this.tokens.indexOf(n1.name);
                            }
                        case PrologOperatorSet.XFX:
                        case PrologOperatorSet.YFX:
                            if (n2.fixity == PrologOperatorSet.XFY) {
                                return -1;
                            }
                            if (n2.fixity == PrologOperatorSet.XFX || n2.fixity == PrologOperatorSet.YFX) {
                                return PrologTermBuilder.this.tokens.indexOf(n1.name) - PrologTermBuilder.this.tokens.indexOf(n2.name);
                            }
                            if (n2.fixity == PrologOperatorSet.YF || n2.fixity == PrologOperatorSet.XF) {
                                return -1;
                            }
                            return 1;
                        case PrologOperatorSet.YF:
                        case PrologOperatorSet.XF:
                            if (n2.fixity == PrologOperatorSet.FX || n2.fixity == PrologOperatorSet.FY || n2.fixity == PrologOperatorSet.XFX || n2.fixity == PrologOperatorSet.XFY || n2.fixity == PrologOperatorSet.YFX) {
                                return 1;
                            }
                            return PrologTermBuilder.this.tokens.indexOf(n2.name) - PrologTermBuilder.this.tokens.indexOf(n1.name);
                    }
                    return 0;
                } else {
                    return n2.precedence - n1.precedence;
                }
            }
        };
        this.fixSets = ops.getFixitySets();
        /*
         * For every name that might be an operator an OpNode is stored for every kind of
         * operator that name might be (prefix, infix and postfix).
         */
        for (InternalNode child : this.tokens) {
            if (child instanceof NameNode || child instanceof EmptyListNode || child instanceof CutNode) {
                for (int i = 0; i < 7; i++) { // check the 7 different fixity types
                    if (this.fixSets[i].isOperator(child.getText())) {
                        switch (i) {
                            case 0:
                                this.prefixOps.add(new OpNode(child, this.set.getPrecedence(child.getText(),PrologOperatorSet.FX),PrologOperatorSet.FX));
                                break;
                            case 1:
                                this.prefixOps.add(new OpNode(child, this.set.getPrecedence(child.getText(),PrologOperatorSet.FY),PrologOperatorSet.FY));
                                break;
                            case 2:
                                this.infixOps.add(new OpNode(child, this.set.getPrecedence(child.getText(),PrologOperatorSet.XFX),PrologOperatorSet.XFX));
                                break;
                            case 3:
                                this.infixOps.add(new OpNode(child, this.set.getPrecedence(child.getText(),PrologOperatorSet.XFY),PrologOperatorSet.XFY));
                                break;
                            case 4:
                                this.infixOps.add(new OpNode(child, this.set.getPrecedence(child.getText(),PrologOperatorSet.YFX),PrologOperatorSet.YFX));
                                break;
                            case 5:
                                this.postfixOps.add(new OpNode(child, this.set.getPrecedence(child.getText(),PrologOperatorSet.XF),PrologOperatorSet.XF));
                                break;
                            case 6:
                                this.postfixOps.add(new OpNode(child, this.set.getPrecedence(child.getText(),PrologOperatorSet.YF),PrologOperatorSet.YF));
                                break;
                            default:
                                throw new IllegalStateException("Unexpected int value in for-loop!");
                        }
                    }
                }
            }
        }
        Collections.sort(this.prefixOps,this.comp);
        Collections.sort(this.infixOps,this.comp);
        Collections.sort(this.postfixOps,this.comp);
    }

//------------------------ public methods ------------------------

    /**
     * Builds terms out of the token list specified in the contructor
     * call. The token list will be changed to a non-complete syntax tree
     * afterwards and further calls of this method will not have any
     * consequences. Possible syntax errors are not checked by this
     * method. In case of wrong syntax the tokens are built to constant
     * terms which can easily be checked for correctness afterwards,
     * because no two terms of which no one is argument to the other can
     * be in one sentence.
     * @throws IllegalStateException If the operator declarations contain
     *                               a declaration with an unknown fixity.
     */
    public void build () throws IllegalStateException {
        ArrayList<OpNode> firsts = new ArrayList<OpNode>();
        while (!(this.prefixOps.isEmpty() && this.infixOps.isEmpty() && this.postfixOps.isEmpty())) {
            firsts.clear();
            if (!this.prefixOps.isEmpty()) {
                firsts.add(this.prefixOps.get(0));
            }
            if (!this.infixOps.isEmpty()) {
                firsts.add(this.infixOps.get(0));
            }
            if (!this.postfixOps.isEmpty()) {
                firsts.add(this.postfixOps.get(0));
            }
            OpNode op = Collections.min(firsts,this.comp);
            int index = this.tokens.indexOf(op.name);
            boolean out = true;
            switch (op.fixity) {
                case PrologOperatorSet.FX:
                case PrologOperatorSet.FY:
                    if (this.buildPrefix(op,index)) {
                        this.deleteInfix(op);
                        this.deletePostfix(op);
                        out = false;
                    }
                    this.deletePrefix(op);
                    break;
                case PrologOperatorSet.XFX:
                case PrologOperatorSet.YFX:
                case PrologOperatorSet.XFY:
                    if (this.buildInfix(op,index)) {
                        this.deletePrefix(op);
                        this.deletePostfix(op);
                        out = false;
                    }
                    this.deleteInfix(op);
                    break;
                case PrologOperatorSet.YF:
                case PrologOperatorSet.XF:
                    if (this.buildPostfix(op,index)) {
                        this.deletePrefix(op);
                        this.deleteInfix(op);
                        out = false;
                    }
                    this.deletePostfix(op);
                    break;
                default:
                    throw new IllegalStateException("Unknown fixity!");
            }
            if (out) {
                for (OpNode o : this.prefixOps) {
                    if (o.name.equals(op.name)) {
                        out = false;
                        break;
                    }
                }
                if (out) {
                    for (OpNode o : this.infixOps) {
                        if (o.name.equals(op.name)) {
                            out = false;
                            break;
                        }
                    }
                    if (out) {
                        for (OpNode o : this.postfixOps) {
                            if (o.name.equals(op.name)) {
                                out = false;
                                break;
                            }
                        }
                        if (out) {
                            this.finalize(op,index);
                        }
                    }
                }
            }
            this.updateOps();
        }
    }

//------------------------ private methods ------------------------

    /**
     * Checks if the token at the specified index can be built to a term
     * by seeing it as an infix operator as specified by the op argument.
     * If so, the term is built and true is returned. Otherwise it will
     * return false and do nothing.
     * @param op The operator declaration.
     * @param index The index of the token in question.
     * @return True if the token was built to a term as infix operator.
     *         False otherwise.
     */
    private boolean buildInfix (OpNode op, int index) {
        if (index == 0 || index == this.tokens.size() - 1) {
            return false;
        }
        boolean low = op.precedence < 1000,
                lowEnough = op.precedence == 1000 && (op.fixity == PrologOperatorSet.XFX || op.fixity == PrologOperatorSet.XFY),
                okay = false;
        if (low || lowEnough) {
            for (int i = index - 1; i >= 0; i--) {
                if (!(this.tokens.get(i) instanceof LayoutNode)) {
                    if (this.tokens.get(i) instanceof CommaNode || this.isPipe(this.tokens.get(i))) {
                        return false;
                    }
                    okay = true;
                    break;
                }
            }
        } else {
            for (int i = index - 1; i >= 0; i--) {
                if (!(this.tokens.get(i) instanceof LayoutNode)) {
                    if (this.isPipe(this.tokens.get(i))) {
                        return false;
                    }
                    okay = true;
                    break;
                }
            }
        }
        if (okay) {
            okay = false;
            if (low || (op.precedence == 1000 && op.fixity != PrologOperatorSet.XFY)) {
                for (int i = index + 1; i < this.tokens.size(); i++) {
                    if (!(this.tokens.get(i) instanceof LayoutNode)) {
                        if (this.tokens.get(i) instanceof CommaNode || this.isPipe(this.tokens.get(i))) {
                            return false;
                        }
                        okay = true;
                        break;
                    }
                }
            } else {
                for (int i = index + 1; i < this.tokens.size(); i++) {
                    if (!(this.tokens.get(i) instanceof LayoutNode)) {
                        if (this.isPipe(this.tokens.get(i))) {
                            return false;
                        }
                        okay = true;
                        break;
                    }
                }
            }
            if (okay) {
                int start = 0,
                    stop = this.tokens.size();
                if (low || lowEnough) {
                    for (int i = index - 1; i >= 0; i--) {
                        if (this.tokens.get(i) instanceof CommaNode) {
                            start = i + 1;
                            break;
                        } else if (this.isPipe(this.tokens.get(i))) {
                            if (low) {
                                start = i + 1;
                                break;
                            } else {
                                return false;
                            }
                        }
                    }
                } else {
                    for (int i = index - 1; i >= 0; i--) {
                        if (this.isPipe(this.tokens.get(i))) {
                            return false;
                        }
                    }
                }
                if (low || (op.precedence == 1000 && op.fixity != PrologOperatorSet.XFY)) {
                    for (int i = index + 1; i < this.tokens.size(); i++) {
                        if (this.tokens.get(i) instanceof CommaNode) {
                            stop = i;
                            break;
                        } else if (this.isPipe(this.tokens.get(i))) {
                            if (low) {
                                stop = i;
                                break;
                            } else {
                                return false;
                            }
                        }
                    }
                }
                TermNode term = new TermNode(op.name.getText(), op.precedence, op.name.getLine(), op.name.getPos());
                ParanthesisNode left = new OpParanthesisNode(op.name.getLine(), op.name.getPos()),
                                right = new OpParanthesisNode(op.name.getLine(), op.name.getPos());
                boolean emptyLeft = true;
                for (int i = start; i < index; i++) {
                    InternalNode arg = this.tokens.get(i);
                    if (emptyLeft && !(arg instanceof LayoutNode)) {
                        emptyLeft = false;
                    }
                    left.addChild(arg);
                }
                if (emptyLeft) {
                    return false;
                }
                boolean emptyRight = true;
                for (int i = index + 1; i < stop; i++) {
                    InternalNode arg = this.tokens.get(i);
                    if (emptyRight && !(arg instanceof LayoutNode)) {
                        emptyRight = false;
                    }
                    right.addChild(this.tokens.get(i));
                }
                if (emptyRight) {
                    return false;
                }
                term.addChild(left);
                term.addChild(right);
                this.tokens.set(index,term);
                this.tokens.removeAll(right.getChildren());
                this.tokens.removeAll(left.getChildren());
                return true;
            }
        }
        return false;
    }

    /**
     * Checks if the token at the specified index can be built to a term
     * by seeing it as a postfix operator as specified by the op argument.
     * If so, the term is built and true is returned. Otherwise it will
     * return false and do nothing.
     * @param op The operator declaration.
     * @param index The index of the token in question.
     * @return True if the token was built to a term as postfix operator.
     *         False otherwise.
     */
    private boolean buildPostfix (OpNode op, int index) {
        boolean low = op.precedence < 1000;
        if (index < this.tokens.size() - 1) {
            for (int i = index + 1; i < this.tokens.size(); i++) {
                if (low && (this.tokens.get(i) instanceof CommaNode || this.isPipe(this.tokens.get(i)))) {
                    break;
                }
                if (!(this.tokens.get(i) instanceof LayoutNode)) {
                    return false;
                }
            }
        }
        if (index > 0) {
            InternalNode next = this.tokens.get(index - 1);
            if (next instanceof LayoutNode) {
                if (index > 1) {
                    next = this.tokens.get(index - 2);
                }
            }
            if (!(next instanceof LayoutNode)) {
                int limit = -1;
                if (low || (op.precedence == 1000 && op.fixity == PrologOperatorSet.XF)) {
                    for (int i = this.tokens.indexOf(next); i > -1; i--) {
                        InternalNode akt = this.tokens.get(i);
                        if (akt instanceof CommaNode) {
                            limit = i;
                            break;
                        } else if (this.isPipe(akt)) {
                            if (low) {
                                limit = i;
                                break;
                            } else {
                                return false;
                            }
                        }
                    }
                }
                TermNode term = new TermNode(op.name.getText(), op.precedence, op.name.getLine(), op.name.getPos());
                ArrayList<InternalNode> args = new ArrayList<InternalNode>();
                boolean emptyArguments = true;
                for (int i = index - 1; i > limit; i--) {
                    InternalNode arg = this.tokens.get(i);
                    if (emptyArguments && !(arg instanceof LayoutNode)) {
                        emptyArguments = false;
                    }
                    args.add(arg);
                }
                if (emptyArguments) {
                    return false;
                }
                for (int i = args.size() - 1; i >= 0; i--) {
                    term.addChild(args.get(i));
                }
                this.tokens.remove(op.name);
                this.tokens.removeAll(term.getChildren());
                this.tokens.add(limit + 1,term);
                return true;
            }
        }
        return false;
    }

    /**
     * Checks if the token at the specified index can be built to a term
     * by seeing it as a prefix operator as specified by the op argument.
     * If so, the term is built and true is returned. Otherwise it will
     * return false and do nothing.
     * @param op The operator declaration.
     * @param index The index of the token in question.
     * @return True if the token was built to a term as prefix operator.
     *         False otherwise.
     */
    private boolean buildPrefix (OpNode op, int index) {
        boolean low = op.precedence < 1000;
        if (index > 0) {
            for (int i = index - 1; i >= 0; i--) {
                if (this.isPipe(this.tokens.get(i))) {
                    if (low) {
                        break;
                    } else {
                        return false;
                    }
                }
                if ((low || op.precedence == 1000) && this.tokens.get(i) instanceof CommaNode) {
                    break;
                }
                if (!(this.tokens.get(i) instanceof LayoutNode)) {
                    if ((index - i == 1) || (index - i == 2 && this.tokens.get(index-1) instanceof LayoutNode)) {
                        // i-th token is the (non-layout) one before the token at index
                        InternalNode n = this.tokens.get(i);
                        boolean notokay = true;
                        for (OpNode o : this.infixOps) {
                            if (o.name.equals(n)) {
                                if (o.fixity == PrologOperatorSet.XFY && o.precedence == op.precedence) {
                                    notokay = false;
                                }
                                break;
                            }
                        }
                        if (notokay) {
                            return false;
                        }
                    } else {
                        return false;
                    }
                }
            }
        }
        if (this.tokens.size() > index + 1) {
            InternalNode next = this.tokens.get(index + 1);
            if ((next instanceof IntNode || next instanceof FloatNode || next instanceof NanNode || next instanceof InfNode) && !next.getText().startsWith("+") && !next.getText().startsWith("-")) {
                String opName = op.name.getText();
                if (opName.equals("+") || opName.equals("-")) {
                    return false;
                }
            }
            if (next instanceof ParanthesisNode || this.isPipe(next)) {
                return false;
            }
            if (next instanceof LayoutNode) {
                if (this.tokens.size() > index + 2) {
                    next = this.tokens.get(index + 2);
                }
            }
            if (!(next instanceof LayoutNode)) {
                int limit = this.tokens.size();
                if (low) {
                    for (int i = this.tokens.indexOf(next); i < this.tokens.size(); i++) {
                        InternalNode akt = this.tokens.get(i);
                        if (akt instanceof CommaNode || this.isPipe(akt)) {
                            limit = i;
                            break;
                        }
                    }
                } else if (op.precedence == 1000 && op.fixity == PrologOperatorSet.FX) {
                    for (int i = this.tokens.indexOf(next); i < this.tokens.size(); i++) {
                        InternalNode akt = this.tokens.get(i);
                        if (akt instanceof CommaNode || this.isPipe(akt)) {
                            return false;
                        }
                    }
                } else {
                    for (int i = this.tokens.indexOf(next); i < this.tokens.size(); i++) {
                        if (this.isPipe(this.tokens.get(i))) {
                            return false;
                        }
                    }
                }
                TermNode term = new TermNode(op.name.getText(), op.precedence, op.name.getLine(), op.name.getPos());
                ArrayList<InternalNode> args = new ArrayList<InternalNode>();
                boolean emptyArguments = true;
                for (int i = limit - 1; i > index; i--) {
                    InternalNode arg = this.tokens.get(i);
                    if (emptyArguments && !(arg instanceof LayoutNode)) {
                        emptyArguments = false;
                    }
                    args.add(arg);
                }
                if (emptyArguments) {
                    return false;
                }
                for (int i = args.size() - 1; i >= 0; i--) {
                    term.addChild(args.get(i));
                }
                this.tokens.removeAll(term.getChildren());
                this.tokens.set(index,term);
                return true;
            }
        }
        return false;
    }

    /**
     * Removes the specified OpNode from the prefix operator list.
     * @param op The OpNode to remove.
     */
    private void deletePrefix (OpNode op) {
        OpNode del = null;
        for (OpNode o : this.prefixOps) {
            if (o.name.equals(op.name)) {
                del = o;
                break;
            }
        }
        if (del != null) {
            this.prefixOps.remove(del);
        }
    }

    /**
     * Removes the specified OpNode from the infix operator list.
     * @param op The OpNode to remove.
     */
    private void deleteInfix (OpNode op) {
        OpNode del = null;
        for (OpNode o : this.infixOps) {
            if (o.name.equals(op.name)) {
                del = o;
                break;
            }
        }
        if (del != null) {
            this.infixOps.remove(del);
        }
    }

    /**
     * Removes the specified OpNode from the postfix operator list.
     * @param op The OpNode to remove.
     */
    private void deletePostfix (OpNode op) {
        OpNode del = null;
        for (OpNode o : this.postfixOps) {
            if (o.name.equals(op.name)) {
                del = o;
                break;
            }
        }
        if (del != null) {
            this.postfixOps.remove(del);
        }
    }

    /**
     * Builds a constant term or a number out of the specified OpNode at
     * the specified index.
     * @param op The OpNode to finalize.
     * @param index The index of the token which belongs to the OpNode.
     */
    private void finalize (OpNode op, int index) {
        if (this.tokens.size() > index + 1) {
            InternalNode next = this.tokens.get(index + 1);
            if (next instanceof ParanthesisNode) {
                TermNode term = new TermNode(op.name.getText(), 0, op.name.getLine(), op.name.getPos());
                List<InternalNode> nodes = next.getChildren();
                for (InternalNode n : nodes) {
                    term.addChild(n);
                }
                this.tokens.remove(next);
                this.tokens.set(index, term);
                return;
            }
            String opName = op.name.getText();
            if (opName.equals("+") || opName.equals("-")) {
                if (next instanceof IntNode) {
                    IntNode newNode = new IntNode(opName + next.getText(), op.name.getLine(), op.name.getPos());
                    this.tokens.remove(next);
                    this.tokens.set(index,newNode);
                    return;
                }
                if (next instanceof FloatNode) {
                    FloatNode newNode = new FloatNode(opName + next.getText(), op.name.getLine(), op.name.getPos());
                    this.tokens.remove(next);
                    this.tokens.set(index,newNode);
                    return;
                }
                if (next instanceof NanNode) {
                    NanNode newNode = new NanNode(opName + next.getText(), op.name.getLine(), op.name.getPos());
                    this.tokens.remove(next);
                    this.tokens.set(index,newNode);
                    return;
                }
                if (next instanceof InfNode) {
                    InfNode newNode = new InfNode(opName + next.getText(), op.name.getLine(), op.name.getPos());
                    this.tokens.remove(next);
                    this.tokens.set(index,newNode);
                    return;
                }
            }
        }
        this.tokens.set(index,new TermNode(op.name.getText(), 0, op.name.getLine(), op.name.getPos()));
    }

    /**
     * Checks whether or not the specified token is a pipe.
     * @param node The token to check.
     * @return True if the token is a pipe. False otherwise.
     */
    private boolean isPipe (InternalNode node) {
        return node instanceof PunctuationNode && node.getText().equals("|");
    }

    /**
     * Removes all OpNodes from the three possible operator lists which
     * do not appear in the token list anymore (i.e. after the certain
     * operator has been built to any kind of term as functor or
     * as an argument).
     */
    private void updateOps () {
        ArrayList<OpNode> toDel = new ArrayList<OpNode>();
        for (OpNode o : this.prefixOps) {
            if (this.tokens.indexOf(o.name) == -1) {
                toDel.add(o);
            }
        }
        this.prefixOps.removeAll(toDel);
        toDel.clear();
        for (OpNode o : this.infixOps) {
            if (this.tokens.indexOf(o.name) == -1) {
                toDel.add(o);
            }
        }
        this.infixOps.removeAll(toDel);
        toDel.clear();
        for (OpNode o : this.postfixOps) {
            if (this.tokens.indexOf(o.name) == -1) {
                toDel.add(o);
            }
        }
        this.postfixOps.removeAll(toDel);
    }

//------------------------ private classes ------------------------

    /**
     * An OpNode stores additional information to a name token.
     * This information concerns the declaration of the name as an
     * operator.<br><br>
     *
     * Created: 01.06.2006<br>
     * Last modified: 11.07.2006
     *
     * @author cryingshadow
     * @version $Id$
     */
    private class OpNode {
        private InternalNode name;
        private int precedence,
                    fixity;

        /**
         * Constructs an OpNode with the specified name token, precedence
         * and fixity.
         * @param name The name token.
         * @param pre The precedence.
         * @param fix The fixity.
         */
        public OpNode (InternalNode name, int pre, int fix) {
            this.name = name;
            this.precedence = pre;
            this.fixity = fix;
        }

    }
}
