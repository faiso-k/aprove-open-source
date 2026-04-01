package aprove.input.Programs.ipad;
import aprove.input.Generated.ipad.node.*;
import aprove.verification.oldframework.Syntax.*;

class TransformPass extends Pass {

    private boolean hasSeenReturn;
    private Sort curReturnSort;
    private ProcHead curProcHead;

    @Override
    public void inAFunct(AFunct node) {
    String name = this.chop(node.getFunctname());
    this.curProcHead = (ProcHead)this.procHeads.get(name);
    this.curReturnSort = this.curProcHead.getSort();
    this.hasSeenReturn = false;
    }

    @Override
    public void caseANeStatementlist(ANeStatementlist node) {
    PStatement statement = node.getStatement();
    PNeStatementlist stmtlist = node.getNeStatementlist();
    PNeStatementlist stmtlist2 = null;
    if (this.containsReturn(statement)) {
        if (statement instanceof AReturnStatement) {
        this.insertRetid(node, null, false);
        PTerm retval = ((AReturnStatement)statement).getTerm();
        if (this.curReturnSort != null) {
            if (retval == null) {
            this.addParseError(((AReturnStatement)statement).getReturn(), "return-value missing");
            }
            else {
            ANeStatementlist newlist= new ANeStatementlist(node.getStatement(), node.getNeStatementlist());
            this.insertRetvalue(node, newlist, retval);
            }
        }
        else {
            if (retval != null) {
            this.addParseError(((AReturnStatement)statement).getReturn(), "return-value given in a void-function");
            }
        }
        this.hasSeenReturn = true;
        }
        else if (statement instanceof AWhileStatement) {
        PSterm c = new AConstVarSterm(new TId("#_c"));
        PTerm oldb = new AStermTerm((PSterm)new ABracesSterm(new TOpen(), ((AWhileStatement)statement).getTerm(), new TClose()));
        PTerm newb = (PTerm)new AOperatorAppTerm(c, new TInfixid("&&"), oldb);
        ((AWhileStatement)statement).setTerm(newb);
        if (stmtlist != null) {
            c = new AConstVarSterm(new TId("#_c"));
            AIfthenStatement newif = new AIfthenStatement(new TIf(), (PTerm)new AStermTerm(c), new TBopen(), new ANonEmptyStatementlist(stmtlist), new TBclose());
            node.setNeStatementlist(new ANeStatementlist(newif, null));
            stmtlist = Pass.getStatementlist(newif.getThenstmt());
        }
        }
        else if (statement instanceof AIfthenStatement) {
        AIfthenStatement oif = (AIfthenStatement)statement;
        if (stmtlist != null) {
            AIfthenelseStatement nif = new AIfthenelseStatement(new TIf(), oif.getCondstmt(), new TBopen(), oif.getThenstmt(), new TBclose(), new TElse(), new TBopen(), new ANonEmptyStatementlist(stmtlist), new TBclose());
            stmtlist = Pass.getStatementlist(nif.getThenstmt());
            stmtlist2 = Pass.getStatementlist(nif.getElsestmt());
            node.setStatement((PStatement)nif);
            node.setNeStatementlist(null);
        }
        }
        if (statement instanceof AIfthenelseStatement) {
        AIfthenelseStatement ifstmt = (AIfthenelseStatement)statement;
        PNeStatementlist thenstmt = Pass.getStatementlist(ifstmt.getThenstmt());
        PNeStatementlist elsestmt = Pass.getStatementlist(ifstmt.getElsestmt());
        if (this.containsReturn(thenstmt)) {
            if (this.containsReturn(elsestmt)) {
            node.setNeStatementlist(null);
            stmtlist = null;
            }
            else {
            this.concatStmtlists(elsestmt, stmtlist);
            }
        }
        else {
            this.concatStmtlists(thenstmt, stmtlist);
        }
        }
        if (!this.hasSeenReturn) {
        ANeStatementlist newlist = new ANeStatementlist(node.getStatement(), node.getNeStatementlist());
        this.insertRetid(node, newlist, true);
        }
        this.hasSeenReturn = true;
    }
    statement.apply(this);
    if (stmtlist != null) {
        stmtlist.apply(this);
    }
    if (stmtlist2 != null) {
        stmtlist2.apply(this);
    }
    }

    private void insertRetid(ANeStatementlist node, PNeStatementlist next, boolean b) {
    TId retid = new TId("#_c");
    AType bool = this.hasSeenReturn ? null : new AType(new TId("bool"));
    PTerm bt = new AStermTerm((PSterm)new AConstVarSterm(new TId(b ? "true" : "false")));
    AAssignSimpleStatement ret = new AAssignSimpleStatement(bool, retid, new TEqual(), bt);
    node.setStatement(new ASimpleStatement(ret, new TSemicolon()));
    node.setNeStatementlist(next);
    }

    private void insertRetvalue(ANeStatementlist node, PNeStatementlist next, PTerm t) {
    TId retid = new TId("#_v");
    AAssignSimpleStatement ret = new AAssignSimpleStatement(null, retid, new TEqual(), t);
    node.setStatement(new ASimpleStatement(ret, new TSemicolon()));
    node.setNeStatementlist(next);
    }

    private boolean containsReturn(Node node) {
    if (node instanceof AReturnStatement) {
        return true;
    }
    if (node instanceof AIfthenelseStatement) {
        Node ts = ((AIfthenelseStatement)node).getThenstmt();
        Node es = ((AIfthenelseStatement)node).getElsestmt();
        return this.containsReturn(ts) || this.containsReturn(es);
    }
    if (node instanceof AIfthenStatement) {
        return this.containsReturn(((AIfthenStatement)node).getThenstmt());
    }
    if (node instanceof AWhileStatement) {
        return this.containsReturn(((AWhileStatement)node).getStatementlist());
    }
    if (node instanceof AEmptyStatementlist) {
        return false;
    }
    if (node instanceof ANonEmptyStatementlist) {
        return this.containsReturn(((ANonEmptyStatementlist)node).getNeStatementlist());
    }
    if (node instanceof ANeStatementlist) {
        Node stmt = ((ANeStatementlist)node).getStatement();
        Node stmtlist = ((ANeStatementlist)node).getNeStatementlist();
        return this.containsReturn(stmt) || this.containsReturn(stmtlist);
    }
    return false;
    }
}
