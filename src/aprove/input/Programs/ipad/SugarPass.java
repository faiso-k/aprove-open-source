package aprove.input.Programs.ipad;

import aprove.input.Generated.ipad.node.*;

/** Treewalker that transforms the syntactic sugar into simple ipad.
 *  (E.g. "do { P } while (b)" becomes "{ P } while (b) { P }".)
 *  @author Christian Haselbach
 *  @version $Id$
 */

class SugarPass extends Pass {

    @Override
    public void caseANeStatementlist(final ANeStatementlist node) {
    final PStatement stmt = node.getStatement();
        final PNeStatementlist stmtlist = node.getNeStatementlist();
        if (stmt instanceof ADoWhileStatement) {
            stmt.apply(this);
            this.makeWhileStatement((ADoWhileStatement) stmt, node);
        } else if (stmt instanceof AForStatement) {
            stmt.apply(this);
            this.makeWhileStatement((AForStatement) stmt, node);
        } else {
            stmt.apply(this);
        }
        if (stmtlist != null) {
            stmtlist.apply(this);
        }
    }

    public void makeWhileStatement(final ADoWhileStatement stmt, final ANeStatementlist stmtlist) {
    final PTerm cond =
            new AStermTerm(new ABracesSterm(new TOpen(), stmt.getTerm(),
                new TClose()));
        final PNeStatementlist whilestmtlist =
            Pass.getStatementlist(stmt.getStatementlist());
        if (whilestmtlist == null) {
            stmtlist.setStatement(new AWhileStatement(new TWhile(), cond,
                new TBopen(), new AEmptyStatementlist(), new TBclose()));
        } else {
            final AWhileStatement whilestmt =
                new AWhileStatement(new TWhile(), cond, new TBopen(),
                    new ANonEmptyStatementlist(whilestmtlist), new TBclose());
            final ABlockStatement prestmt = new ABlockStatement();
            prestmt.setStatementlist(new ANonEmptyStatementlist(
                (ANeStatementlist) whilestmtlist.clone()));
            stmtlist.setStatement(prestmt);
            final ANeStatementlist newlist =
                new ANeStatementlist(whilestmt, stmtlist.getNeStatementlist());
            stmtlist.setNeStatementlist(newlist);
        }
    }

    public void makeWhileStatement(final AForStatement stmt, final ANeStatementlist stmtlist) {
    final ASimpleStatement init =
            new ASimpleStatement(stmt.getInit(), new TSemicolon());
        PTerm cond = stmt.getCond();
        if (cond == null) {
            cond = new AStermTerm(new AConstVarSterm(new TId("true")));
        }
        final ASimpleStatement endstmt =
            new ASimpleStatement(stmt.getEnd(), new TSemicolon());
        final PNeStatementlist whilestmtlist =
            Pass.getStatementlist(stmt.getStatementlist());
        if (endstmt.getSimpleStatement() != null) {
            this.concatStmtlists(whilestmtlist, new ANeStatementlist(endstmt,
                null));
        }
        final PStatement whilestmt =
            new AWhileStatement(new TWhile(), cond, new TBopen(),
                new ANonEmptyStatementlist(whilestmtlist), new TBclose());
        PStatement block = whilestmt;
        if (init.getSimpleStatement() != null) {
            block =
                new ABlockStatement(new TBopen(), new ANonEmptyStatementlist(
                    new ANeStatementlist(init, new ANeStatementlist(whilestmt,
                        null))), new TBclose());
        }
        stmtlist.setStatement(block);
    }
}
