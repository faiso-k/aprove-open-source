package aprove.input.Programs.prolog;

import java.util.*;
import java.util.logging.*;

import aprove.input.Generated.prolog.analysis.*;
import aprove.input.Generated.prolog.node.*;
import aprove.input.Programs.prolog.nodes.*;

/**
 * LayoutPass.<br><br>
 *
 * Created: Sep 28, 2006<br>
 * Last modified: Sep 28, 2006
 *
 * @author cryingshadow
 * @version $Id$
 */
public class TriplePass extends DepthFirstAdapter {

    protected static Logger logger =
        Logger.getLogger("aprove.verification.dpframework.PROLOGProblem.Processors");

    private ArrayList<String> layout;
    private PrologOperatorSet ops;
    private ProgramNode rootTriples;
    private ProgramNode rootClauses;
    private Map<Node, InternalNode> nodes;
    private boolean opdefs;
    private boolean triples;

    public TriplePass() {
        this.layout = new ArrayList<String>();
        this.ops = PrologOperatorSet.createStandardSet();
        this.rootTriples = new ProgramNode();
        this.rootClauses = new ProgramNode();
        this.nodes = new LinkedHashMap<Node, InternalNode>();
        this.opdefs = true;
        this.triples = false;
    }

    public ArrayList<String> getLayout() {
        return this.layout;
    }

    /**
     * @return
     */
    public ProgramNode getTripleRoot() {
        return this.rootTriples;
    }

    public ProgramNode getClauseRoot() {
        return this.rootClauses;
    }

    /**
     * @return
     */
    public PrologOperatorSet getOperatorSet() {
        return this.ops;
    }

    @Override
    public void caseASentence(ASentence s) {
        this.inASentence(s);
        List<PAny> list = s.getAny();
        for (PAny any : list) {
            if (any instanceof ATokenAny) {
                PToken token = ((ATokenAny) any).getToken();
                if (token instanceof ALayoutToken) {
                    String text =
                        ((ALayoutToken) token).getLayoutText().getText().trim();
                    if (!text.equals("")) {
                        this.layout.add(text);
                        this.tripleSwitch(text);
                    }
                }
            }
        }
        if (this.opdefs) {
            this.opdefs = false;
            //            List<PAny> list = s.getAny();
            int i = 0;
            PAny any = list.get(i);
            PToken akt = null;
            if (any instanceof ATokenAny) {
                akt = ((ATokenAny) any).getToken();
                if (akt instanceof ALayoutToken) {
                    i++;
                    any = list.get(i);
                    if (any instanceof ATokenAny) {
                        akt = ((ATokenAny) any).getToken();
                    }
                }
                if (akt instanceof ANameToken) {
                    if (((ANameToken) akt).getName().getText().equals(":-")) {
                        i++;
                        any = list.get(i);
                        if (any instanceof ATokenAny) {
                            akt = ((ATokenAny) any).getToken();
                            if (akt instanceof ALayoutToken
                                    || (akt instanceof APunctuationToken && ((APunctuationToken) akt).getPunctuationChar().getText().equals(
                                    "("))) {
                                i++;
                                any = list.get(i);
                                if (any instanceof ATokenAny) {
                                    akt = ((ATokenAny) any).getToken();
                                }
                            }
                            if (akt instanceof ALayoutToken) {
                                i++;
                                any = list.get(i);
                                if (any instanceof ATokenAny) {
                                    akt = ((ATokenAny) any).getToken();
                                }
                            }
                            if (akt instanceof ANameToken) {
                                if (((ANameToken) akt).getName().getText().equals(
                                "op")) {
                                    TName decl = ((ANameToken) akt).getName();
                                    int fin = this.checkOpDef(list, i);
                                    if (fin >= 0) {
                                        this.extractOpDef(list, i, fin);
                                        i = fin + 1;
                                        if (list.size() > i) {
                                            boolean error = true;
                                            any = list.get(i);
                                            if (any instanceof ATokenAny) {
                                                akt =
                                                    ((ATokenAny) any).getToken();
                                                if (akt instanceof ALayoutToken) {
                                                    if (list.size() == i + 1) {
                                                        error = false;
                                                    }
                                                }
                                            }
                                            if (error) {
                                                throw new PrologSyntaxException(
                                                    "Unexpected tokens after operator declaration!("
                                                    + decl.getLine() + ", "
                                                    + decl.getPos() + ")");
                                            }
                                        }
                                        this.opdefs = true;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        if (!this.opdefs) {
            boolean foundLater = false;
            //            List<PAny> list = s.getAny();
            int i = 0;
            PAny any = list.get(i);
            PToken akt = null;
            if (any instanceof ATokenAny) {
                akt = ((ATokenAny) any).getToken();
                if (akt instanceof ALayoutToken) {
                    i++;
                    any = list.get(i);
                    if (any instanceof ATokenAny) {
                        akt = ((ATokenAny) any).getToken();
                    }
                }
                if (akt instanceof ANameToken) {
                    if (((ANameToken) akt).getName().getText().equals(":-")) {
                        i++;
                        any = list.get(i);
                        if (any instanceof ATokenAny) {
                            akt = ((ATokenAny) any).getToken();
                            if (akt instanceof ALayoutToken
                                    || (akt instanceof APunctuationToken && ((APunctuationToken) akt).getPunctuationChar().getText().equals(
                                    "("))) {
                                i++;
                                any = list.get(i);
                                if (any instanceof ATokenAny) {
                                    akt = ((ATokenAny) any).getToken();
                                }
                            }
                            if (akt instanceof ALayoutToken) {
                                i++;
                                any = list.get(i);
                                if (any instanceof ATokenAny) {
                                    akt = ((ATokenAny) any).getToken();
                                }
                            }
                            if (akt instanceof ANameToken) {
                                if (((ANameToken) akt).getName().getText().equals(
                                "op")) {
                                    TName decl = ((ANameToken) akt).getName();
                                    int fin = this.checkOpDef(list, i);
                                    if (fin >= 0) {
                                        TriplePass.logger.log(
                                            Level.WARNING,
                                        "Found operator declarations not at the beginning of the program. They will be treated as if they were at the beginning of the program!");
                                        this.extractOpDef(list, i, fin);
                                        i = fin + 1;
                                        if (list.size() > i) {
                                            boolean error = true;
                                            any = list.get(i);
                                            if (any instanceof ATokenAny) {
                                                akt =
                                                    ((ATokenAny) any).getToken();
                                                if (akt instanceof ALayoutToken) {
                                                    if (list.size() == i + 1) {
                                                        error = false;
                                                    }
                                                }
                                            }
                                            if (error) {
                                                throw new PrologSyntaxException(
                                                    "Unexpected tokens after operator declaration!("
                                                    + decl.getLine() + ", "
                                                    + decl.getPos() + ")");
                                            }
                                        }
                                        foundLater = true;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            if (!foundLater) {
                SentenceNode newNode =
                    new SentenceNode(s.getFullstop().getLine(),
                        s.getFullstop().getPos());
                this.getRoot().addChild(newNode);
                this.nodes.put(s, newNode);
                List<PAny> copy = new ArrayList<PAny>(s.getAny());
                for (PAny e : copy) {
                    e.apply(this);
                }
            }
        }
        String fullstopText = s.getFullstop().getText().substring(1).trim();
        if (!fullstopText.equals("")) {
            this.layout.add(fullstopText);
            this.tripleSwitch(fullstopText);
        }
        this.outASentence(s);
    }

    private void tripleSwitch(String text) {
        {
            int pos = text.indexOf("triples:");
            while (pos >= 0) {
                pos--;
                switch (text.charAt(pos)) {
                case '%':
                    this.triples = true;
                    return;
                case ' ':
                    continue;
                }
                break;
            }
        }
        {
            int pos = text.indexOf("clauses:");
            while (pos >= 0) {
                pos--;
                switch (text.charAt(pos)) {
                case '%':
                    this.triples = false;
                    return;
                case ' ':
                    continue;
                }
                break;
            }
        }
    }

    private ProgramNode getRoot() {
        if (this.triples) {
            return this.rootTriples;
        } else {
            return this.rootClauses;
        }
    }

    @Override
    public void caseATokenAny(ATokenAny node) {
        this.inATokenAny(node);
        Node par = node.parent();
        InternalNode parent = this.nodes.get(par);
        InternalNode newNode = null;
        PToken token = node.getToken();
        if (token != null) {
            if (token instanceof AEmptylistToken) {
                TEmptyList aToken = ((AEmptylistToken) token).getEmptyList();
                newNode = new EmptyListNode(aToken.getLine(), aToken.getPos());
            } else if (token instanceof ACutToken) {
                TCutSym aToken = ((ACutToken) token).getCutSym();
                newNode = new CutNode(aToken.getLine(), aToken.getPos());
            } else if (token instanceof AInfToken) {
                TInfinity aToken = ((AInfToken) token).getInfinity();
                newNode = new InfNode(aToken.getLine(), aToken.getPos());
            } else if (token instanceof ANanToken) {
                TNoNumber aToken = ((ANanToken) token).getNoNumber();
                newNode = new NanNode(aToken.getLine(), aToken.getPos());
            } else if (token instanceof ACommaToken) {
                TComma aToken = ((ACommaToken) token).getComma();
                newNode = new CommaNode(aToken.getLine(), aToken.getPos());
            } else if (token instanceof APunctuationToken) {
                TPunctuationChar aToken =
                    ((APunctuationToken) token).getPunctuationChar();
                newNode =
                    new PunctuationNode(
                        ((APunctuationToken) token).getPunctuationChar().getText(),
                        aToken.getLine(), aToken.getPos());
            } else if (token instanceof ANameToken) {
                TName aToken = ((ANameToken) token).getName();
                newNode =
                    new NameNode(((ANameToken) token).getName().getText(),
                        aToken.getLine(), aToken.getPos());
            } else if (token instanceof AIntToken) {
                TInt aToken = ((AIntToken) token).getInt();
                newNode =
                    new IntNode(((AIntToken) token).getInt().getText(),
                        aToken.getLine(), aToken.getPos());
            } else if (token instanceof AFloatToken) {
                TUnsignedFloat aToken =
                    ((AFloatToken) token).getUnsignedFloat();
                newNode =
                    new FloatNode(
                        ((AFloatToken) token).getUnsignedFloat().getText(),
                        aToken.getLine(), aToken.getPos());
            } else if (token instanceof AVariableToken) {
                TVariable aToken = ((AVariableToken) token).getVariable();
                newNode =
                    new VarNode(
                        ((AVariableToken) token).getVariable().getText(),
                        aToken.getLine(), aToken.getPos());
            } else if (token instanceof AStringToken) {
                TString aToken = ((AStringToken) token).getString();
                newNode =
                    new StringNode(
                        ((AStringToken) token).getString().getText(),
                        aToken.getLine(), aToken.getPos());
            } else if (token instanceof ALayoutToken) {
                TLayoutText aToken = ((ALayoutToken) token).getLayoutText();
                newNode = new LayoutNode(aToken.getLine(), aToken.getPos());
            } else {
                throw new IllegalStateException(
                "Unknown token type occured!");
            }
            this.getRoot().addAfter(parent, newNode);
            this.nodes.put(node, newNode);
        }
        this.outATokenAny(node);
    }

    /* (non-Javadoc)
     * @see aprove.input.Generated.prolog.analysis.DepthFirstAdapter#caseAListAny(aprove.input.Generated.prolog.node.AListAny)
     */
    @Override
    public void caseAListAny(AListAny node) {
        this.inAListAny(node);
        PNonemptyList list = node.getNonemptyList();
        if (list instanceof ANonemptyList) {
            Node par = node.parent();
            TBracketL start = ((ANonemptyList) list).getBracketL();
            InternalNode parent = this.nodes.get(par), newNode =
                new ListNode(start.getLine(), start.getPos());
            this.getRoot().addAfter(parent, newNode);
            this.nodes.put(list, newNode);
            List<PAny> copy =
                new ArrayList<PAny>(((ANonemptyList) list).getAny());
            for (PAny e : copy) {
                e.apply(this);
            }
        }
        this.outAListAny(node);
    }

    @Override
    public void caseAConditionAny(AConditionAny node) {
        this.inAConditionAny(node);
        PGrCondition con = node.getGrCondition();
        if (con instanceof AGrCondition) {
            Node par = node.parent();
            TCurlyL start = ((AGrCondition) con).getCurlyL();
            InternalNode parent = this.nodes.get(par), newNode = null;
            newNode = new ConditionNode(start.getLine(), start.getPos());
            this.getRoot().addAfter(parent, newNode);
            this.nodes.put(con, newNode);
            List<PAny> copy =
                new ArrayList<PAny>(((AGrCondition) con).getAny());
            for (PAny e : copy) {
                e.apply(this);
            }
        }
        this.outAConditionAny(node);
    }

    /**
     * @param list
     * @param index
     * @return
     */
    private int checkOpDef(List<PAny> list, int index) {
        int i = index + 1;
        PAny neu = list.get(i);
        if (neu instanceof ATokenAny) {
            PToken akt = ((ATokenAny) neu).getToken();
            if (akt instanceof APunctuationToken) {
                if (((APunctuationToken) akt).getPunctuationChar().getText().equals(
                "(")) {
                    i++;
                    neu = list.get(i);
                    if (neu instanceof ATokenAny) {
                        akt = ((ATokenAny) neu).getToken();
                        if (akt instanceof ALayoutToken) {
                            i++;
                            neu = list.get(i);
                            if (neu instanceof ATokenAny) {
                                akt = ((ATokenAny) neu).getToken();
                            }
                        }
                        if (akt instanceof AIntToken) {
                            i++;
                            neu = list.get(i);
                            if (neu instanceof ATokenAny) {
                                akt = ((ATokenAny) neu).getToken();
                                if (akt instanceof ALayoutToken) {
                                    i++;
                                    neu = list.get(i);
                                    if (neu instanceof ATokenAny) {
                                        akt = ((ATokenAny) neu).getToken();
                                    }
                                }
                                if (akt instanceof ACommaToken) {
                                    i++;
                                    neu = list.get(i);
                                    if (neu instanceof ATokenAny) {
                                        akt = ((ATokenAny) neu).getToken();
                                        if (akt instanceof ALayoutToken) {
                                            i++;
                                            neu = list.get(i);
                                            if (neu instanceof ATokenAny) {
                                                akt =
                                                    ((ATokenAny) neu).getToken();
                                            }
                                        }
                                        if (akt instanceof ANameToken) {
                                            i++;
                                            neu = list.get(i);
                                            if (neu instanceof ATokenAny) {
                                                akt =
                                                    ((ATokenAny) neu).getToken();
                                                if (akt instanceof ALayoutToken) {
                                                    i++;
                                                    neu = list.get(i);
                                                    if (neu instanceof ATokenAny) {
                                                        akt =
                                                            ((ATokenAny) neu).getToken();
                                                    }
                                                }
                                                if (akt instanceof ACommaToken) {
                                                    i++;
                                                    neu = list.get(i);
                                                    if (neu instanceof ATokenAny) {
                                                        akt =
                                                            ((ATokenAny) neu).getToken();
                                                        if (akt instanceof ALayoutToken) {
                                                            i++;
                                                            neu = list.get(i);
                                                            if (neu instanceof ATokenAny) {
                                                                akt =
                                                                    ((ATokenAny) neu).getToken();
                                                            }
                                                        }
                                                        if (akt instanceof ANameToken
                                                                || akt instanceof AEmptylistToken
                                                                || akt instanceof ACutToken) {
                                                            i++;
                                                            neu = list.get(i);
                                                            if (neu instanceof ATokenAny) {
                                                                akt =
                                                                    ((ATokenAny) neu).getToken();
                                                                if (akt instanceof ALayoutToken) {
                                                                    i++;
                                                                    neu =
                                                                        list.get(i);
                                                                    if (neu instanceof ATokenAny) {
                                                                        akt =
                                                                            ((ATokenAny) neu).getToken();
                                                                    }
                                                                }
                                                                if (akt instanceof APunctuationToken) {
                                                                    if (((APunctuationToken) akt).getPunctuationChar().getText().equals(
                                                                    ")")) {
                                                                        return i;
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    } else if (neu instanceof AListAny) {
                                                        i++;
                                                        neu = list.get(i);
                                                        if (neu instanceof ATokenAny) {
                                                            akt =
                                                                ((ATokenAny) neu).getToken();
                                                            if (akt instanceof ALayoutToken) {
                                                                i++;
                                                                neu =
                                                                    list.get(i);
                                                                if (neu instanceof ATokenAny) {
                                                                    akt =
                                                                        ((ATokenAny) neu).getToken();
                                                                }
                                                            }
                                                            if (akt instanceof APunctuationToken) {
                                                                if (((APunctuationToken) akt).getPunctuationChar().getText().equals(
                                                                ")")) {
                                                                    return i;
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        return -1;
    }

    /**
     * @param list
     * @param start
     * @param end
     */
    private void extractOpDef(List<PAny> list, int start, int end) {
        int i = start + 2, precedence = -1, fixity = -1;
        String name = "", fix = "";
        PToken akt = ((ATokenAny) list.get(i)).getToken();
        if (akt instanceof ALayoutToken) {
            i++;
            akt = ((ATokenAny) list.get(i)).getToken();
        }
        precedence = Integer.parseInt(((AIntToken) akt).getInt().getText());
        i++;
        akt = ((ATokenAny) list.get(i)).getToken();
        if (akt instanceof ALayoutToken) {
            i++;
        }
        i++;
        akt = ((ATokenAny) list.get(i)).getToken();
        if (akt instanceof ALayoutToken) {
            i++;
            akt = ((ATokenAny) list.get(i)).getToken();
        }
        fix = ((ANameToken) akt).getName().getText();
        if (fix.equals("fx")) {
            fixity = PrologOperatorSet.FX;
        } else if (fix.equals("fy")) {
            fixity = PrologOperatorSet.FY;
        } else if (fix.equals("xfx")) {
            fixity = PrologOperatorSet.XFX;
        } else if (fix.equals("xfy")) {
            fixity = PrologOperatorSet.XFY;
        } else if (fix.equals("yfx")) {
            fixity = PrologOperatorSet.YFX;
        } else if (fix.equals("xf")) {
            fixity = PrologOperatorSet.XF;
        } else if (fix.equals("yf")) {
            fixity = PrologOperatorSet.YF;
        } else {
            TName tok = ((ANameToken) akt).getName();
            throw new PrologSyntaxException(
                "Unknown fixity in operator declaration!(" + tok.getLine()
                + ", " + tok.getPos() + ")");
        }
        i++;
        akt = ((ATokenAny) list.get(i)).getToken();
        if (akt instanceof ALayoutToken) {
            i++;
        }
        i++;
        PAny opName = list.get(i);
        if (opName instanceof AListAny) {
            List<PAny> opList =
                ((ANonemptyList) ((AListAny) opName).getNonemptyList()).getAny();
            int opened = 0;
            for (PAny any : opList) {
                if (opened < 0) {
                    TBracketL bracket =
                        ((ANonemptyList) ((AListAny) opName).getNonemptyList()).getBracketL();
                    throw new PrologSyntaxException(
                        "Unexpected argument for list of operator names in operator declaration!("
                        + bracket.getLine() + ", " + bracket.getPos() + ")");
                }
                if (any instanceof ATokenAny) {
                    akt = ((ATokenAny) any).getToken();
                    if (akt instanceof ALayoutToken) {
                        continue;
                    } else if (akt instanceof ACommaToken) {
                        if (opened > 0) {
                            TBracketL bracket =
                                ((ANonemptyList) ((AListAny) opName).getNonemptyList()).getBracketL();
                            throw new PrologSyntaxException(
                                "Unexpected argument for list of operator names in operator declaration!("
                                + bracket.getLine() + ", "
                                + bracket.getPos() + ")");
                        }
                        continue;
                    } else if (akt instanceof APunctuationToken) {
                        String text =
                            ((APunctuationToken) akt).getPunctuationChar().getText();
                        if (text.equals("(")) {
                            opened++;
                            continue;
                        } else if (text.equals(")")) {
                            opened--;
                            continue;
                        } else {
                            TBracketL bracket =
                                ((ANonemptyList) ((AListAny) opName).getNonemptyList()).getBracketL();
                            throw new PrologSyntaxException(
                                "Unexpected argument for list of operator names in operator declaration!("
                                + bracket.getLine() + ", "
                                + bracket.getPos() + ")");
                        }
                    } else if (akt instanceof ANameToken) {
                        name = ((ANameToken) akt).getName().getText();
                        this.ops.add(precedence, fixity, name);
                    } else if (akt instanceof AEmptylistToken) {
                        this.ops.add(precedence, fixity, "[]");
                    } else if (akt instanceof ACutToken) {
                        this.ops.add(precedence, fixity, "!");
                    } else {
                        TBracketL bracket =
                            ((ANonemptyList) ((AListAny) opName).getNonemptyList()).getBracketL();
                        throw new PrologSyntaxException(
                            "Unexpected argument for list of operator names in operator declaration!("
                            + bracket.getLine() + ", " + bracket.getPos()
                            + ")");
                    }
                } else {
                    TBracketL bracket =
                        ((ANonemptyList) ((AListAny) opName).getNonemptyList()).getBracketL();
                    throw new PrologSyntaxException(
                        "Unexpected argument for list of operator names in operator declaration!("
                        + bracket.getLine() + ", " + bracket.getPos() + ")");
                }
            }
        } else if (((ATokenAny) opName).getToken() instanceof ANameToken) {
            name =
                ((ANameToken) ((ATokenAny) opName).getToken()).getName().getText();
            this.ops.add(precedence, fixity, name);
        } else if (((ATokenAny) opName).getToken() instanceof ACutToken) {
            this.ops.add(precedence, fixity, "!");
        }
    }

}

