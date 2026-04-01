package aprove.input.Programs.haskell;

import java.util.*;

import aprove.input.Generated.haskell.node.*;
import aprove.runtime.*;
import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Declarations.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Literals.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Modules.Module;
import aprove.verification.oldframework.Haskell.Patterns.*;
import aprove.verification.oldframework.Haskell.Qualifiers.*;
import aprove.verification.oldframework.Haskell.Syntax.*;
import aprove.verification.oldframework.Haskell.Typing.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * The HaskellASTBuilder is a DepthFirstAdapter of the Sablecc Generated parser for Haskell.
 * Each syntactic element gets a representation within the haskell framework
 * by using the HaskellFactory and the HaskellSymFactory for creation.
 * Each HaskellObject can carry a token for convenience of error output.
 *
 * Attention: The syntax for haskell records isn't transformed
 *
 *              matraf: now transforming it on the fly
 */

public class HaskellASTBuilder extends ASTBuilder {
    public int fixity;
    public List<Atom> exImpConsAtoms;
    public List<HaskellExport> expList;
    public List<ImpDecl> imps;
    public HaskellFactory fac;
    public HaskellSymFactory symfac;
    public Token curToken;
    public Modules modules;
    public boolean isMain;




    public HaskellASTBuilder(Modules modules,boolean isMain, boolean isPrelude){
        this.modules = modules;
        this.isMain = isMain;
        this.symfac = new HaskellSymFactory(modules);
        this.fac = new HaskellFactory(this.symfac,isPrelude,modules.getPrelude());
    }

    @Override
    public void outAExp(AExp node){
        if(node.getTyped() != null){
            HaskellPreType ho = (HaskellPreType) this.pop();
            RawTerm rt = (RawTerm) this.peek();
            rt.shiftTypeDown(ho);
        }
    }

    @Override
    public void inAExp0(AExp0 node){ this.pushMark(); }
    @Override
    public void outAExp0(AExp0 node){
        List<HaskellObject> list = this.popMarkList();
        this.push(this.fac.buildRawTerm(list));
    }

    @Override
    public void inAExp0b(AExp0b node){ this.pushMark(); }
    @Override
    public void outAExp0b(AExp0b node){
        List<HaskellObject> list = this.popMarkList();
        this.push(this.fac.buildRawTerm(list));
    }

    @Override
    public void inALambdapats(ALambdapats node) { this.pushMode(ASTBuilder.PAT); }
    @Override
    public void outALambdapats(ALambdapats node){ this.popMode(); }
    @Override
    public void inALambdaExptail(ALambdaExptail node) { this.pushMark(); }
    @Override
    public void outALambdaExptail(ALambdaExptail node){
        Token tok = node.getLambda();
        if (!this.isExpMode()) {
            HaskellError.output(tok,"expression expected");
        }
        HaskellExp exp = (HaskellExp) this.pop(); // the last pushed exp
        List<HaskellPat> list = new Vector<HaskellPat>();
        for (HaskellObject ho : this.popMarkList()){
           list.add((HaskellPat)ho);
        }
        this.push(this.fac.buildLambdaExp(list,exp,tok));
    }

    @Override
    public void inALetExptail(ALetExptail node) {
        this.pushMark();
    }

    @Override
    public void outALetExptail(ALetExptail node){
        Token tok = node.getKwlet();
        if (!this.isExpMode()) {
            HaskellError.output(tok,"expression expected");
        }
        HaskellExp exp = (HaskellExp) this.pop();
        List<HaskellDecl> list = new Vector<HaskellDecl>();
        for (HaskellObject ho : this.popMarkList()){
          list.add((HaskellDecl)ho);
        }
        this.push(this.fac.buildLetExp(list,exp,tok));
    }

    @Override
    public void inAIfExptail(AIfExptail node){     this.pushMark(); }
    @Override
    public void outAIfExptail(AIfExptail node){
        Token tok = node.getKwif();
        if (!this.isExpMode()) {
            HaskellError.output(tok,"expression expected");
        }
        HaskellObject[] ho = this.popMarkArray();
        this.push(this.fac.buildIfExp((HaskellExp) ho[0],(HaskellExp) ho[1],(HaskellExp) ho[2],tok));
    }

    @Override
    public void inADoBexp(ADoBexp node){ this.pushMark(); }
    @Override
    public void outADoBexp(ADoBexp node){
        Token tok = node.getKwdo();
        if (!this.isExpMode()) {
            HaskellError.output(tok,"unexpected expression");
        }
        List<HaskellObject> list = this.popMarkList();
        HaskellQual[] arr = new HaskellQual[list.size()];
        int i=0;
        for (HaskellObject ho : list){
           arr[i] = (HaskellQual)ho;
           i++;
        }
        this.push(this.fac.buildMonad(arr));
    }

    @Override
    public void inAMinusBexp(AMinusBexp node){
        Token tok = node.getMinus();
        this.push(this.fac.buildOperator((Var)this.fac.buildVar(this.symfac.negate(tok))));
    }

    @Override
    public void outAMinusBexp(AMinusBexp node){
        HaskellObject ho = this.pop();
    if (ho instanceof IntegerLit){
        this.pop();
        ((IntegerLit)ho).negate();
    } else if (ho instanceof FloatLit){
        this.pop();
        ((FloatLit)ho).negate();
    } else if (!this.isExpMode()) {
            Token tok = node.getMinus();
            HaskellError.output(tok,"unexpected expression");
        }
    this.push(ho);

    }

    @Override
    public void inACaseBexp(ACaseBexp node) { this.pushMark(); }
    @Override
    public void outACaseBexp(ACaseBexp node){
        Token tok = node.getKwcase();
        List<HaskellObject> objs = this.popMarkList();
        HaskellExp exp = (HaskellExp) objs.remove(0);
        List<AltExp> list = new Vector<AltExp>();
        for (HaskellObject ho : objs){
            list.add((AltExp)ho);
        }
        this.push(this.fac.buildCaseExp(tok,exp,list));
    }

    @Override
    public void inADirectAlt(ADirectAlt node){ }
    @Override
    public void outADirectAlt(ADirectAlt node){
        WhereDecls wdecs = null;
        if(node.getWheredecls() != null) { wdecs = (WhereDecls) this.pop();}
        HaskellExp exp = (HaskellExp) this.pop();
        RawTerm altpat = (RawTerm) this.pop();
        this.push(this.fac.buildAltExp(altpat,exp,wdecs));
    }

    @Override
    public void inACondAlt(ACondAlt node){ this.pushMark(); }
    @Override
    public void outACondAlt(ACondAlt node){
        WhereDecls wdecs = null;
        if(node.getWheredecls() != null) { wdecs = (WhereDecls) this.pop();}
        List<HaskellObject> objs = this.popMarkList();
        RawTerm altpat = (RawTerm) objs.remove(0);
        List<CondExp> list = new Vector<CondExp>();
        for (HaskellObject ge : objs){
           list.add((CondExp)ge);
        }
        this.push(this.fac.buildAltExp(altpat,list,wdecs));
    }

    @Override
    public void outAGdpat(AGdpat node){
        HaskellExp exp = (HaskellExp) this.pop();
        HaskellExp guard = (HaskellExp) this.pop();
        this.push(this.fac.buildCondExp(guard,exp));
    }

    @Override
    public void inAAltpat(AAltpat node){ this.pushMode(ASTBuilder.PAT);}
    @Override
    public void outAAltpat(AAltpat node){ this.popMode(); }

    @Override
    public void  inAAtAexp(AAtAexp node){ this.pushMark(); }
    @Override
    public void outAAtAexp(AAtAexp node){
        Token tok = node.getAt();
        if (!this.isPatMode()) {
            HaskellError.output(tok,"unexpected pattern");
        }
        HaskellObject[] ho = this.popMarkArray();
        this.push(this.fac.buildBindPat((Var) ho[0],(HaskellPat) ho[1]));
    }

    @Override
    public void outAIrrAexp(AIrrAexp node){
        Token tok = node.getTilde();
        if (!this.isPatMode()) {
            HaskellError.output(tok,"unexpected pattern");
        }
        this.push(this.fac.buildIrrPat((HaskellPat)this.pop(),tok));
    }

    @Override
    public void caseTInteger(TInteger node){
        this.push(this.fac.buildIntegerLit(node));
    }

    @Override
    public void caseTFloat(TFloat node){
        this.push(this.fac.buildFloatLit(node));
    }

    @Override
    public void caseTStrchar(TStrchar node){
        int i = ASCII.escapeToInt(node.getText());
        if (i == -1)
         {
            return; // ignroe empty char
        }
        if (i == -2) {
            HaskellError.output(node,"unknown escape sequence");
        }
        this.push(this.fac.buildCharLit((char)i,node));
    }

    @Override
    public void caseTCchar(TCchar node){
        int i = ASCII.escapeToInt(node.getText());
        if (i == -1) {
            HaskellError.output(node,"char expected");
        }
        if (i == -2) {
            HaskellError.output(node,"unknown escape sequence");
        }
        this.push(this.fac.buildCharLit((char)i,node));
    }

    @Override
    public void  inAString(AString node){ this.pushMark();  }
    @Override
    public void outAString(AString node){
       HaskellObject[] list = this.popMarkArray();
       this.push(this.fac.buildList(list,node.getStringend()));
    }

    @Override
    public void caseTWildcard(TWildcard node) {
        if (!this.isPatMode()) {
            HaskellError.output(node,"unexpected pattern");
        }
        this.push(this.fac.buildJokerPat(node));
    }

    @Override
    public void  inARightapplyAexp2(ARightapplyAexp2 node){ this.pushMark(); }
    @Override
    public void outARightapplyAexp2(ARightapplyAexp2 node){
        HaskellObject[] ho = this.popMarkArray();
        Token tok = ho[1].getToken();
        if (!this.isExpMode()) {
            HaskellError.output(tok,"unexpected expression");
        }
        Operator op = (Operator) ho[1];
        this.push(this.fac.buildApply(op.getAtom(),ho[0]));
    }

    @Override
    public void inALeftapplyAexp2(ALeftapplyAexp2 node){ this.pushMark(); }
    @Override
    public void outALeftapplyAexp2(ALeftapplyAexp2 node){
        HaskellObject[] ho = this.popMarkArray();
        Token tok = ho[0].getToken();
        if (!this.isExpMode()) {
            HaskellError.output(tok,"unexpected expression");
        }
        Operator op = (Operator) ho[0];
        this.push(this.fac.buildFlipApply(op.getAtom(),ho[1]));
    }

    @Override
    public void outAEmptyAexp2(AEmptyAexp2 node){
        this.push(this.fac.buildCons(this.symfac.tuple(node.getOpen(),0)));
    }

    @Override
    public void inATupleAexp2(ATupleAexp2 node){ this.pushMark(); }
    @Override
    public void outATupleAexp2(ATupleAexp2 node){
        List<HaskellObject>tups = this.popMarkList();
        tups.add(0,this.fac.buildCons(this.symfac.tuple(node.getOpen(),tups.size())));
        this.push(this.fac.buildApplies(tups));
    }


    @Override
    public void  inASingleList(ASingleList node){ this.pushMark();}
    @Override
    public void outASingleList(ASingleList node){
       HaskellObject[] list = this.popMarkArray();
       this.push(this.fac.buildList(list,list[list.length-1].getToken()));
    }

    @Override
    public void  inASomeList(ASomeList node){ this.pushMark();}
    @Override
    public void outASomeList(ASomeList node){
       HaskellObject[] list = this.popMarkArray();
       this.push(this.fac.buildList(list,list[list.length-1].getToken()));
    }

    @Override
    public void outAArithList(AArithList node){
        HaskellObject step = null;
        HaskellObject end = null;
        if(node.getEnd() != null){ end = this.pop(); }
        if(node.getStep() != null){ step = this.pop(); }
        HaskellObject start = this.pop();
        if (!this.isExpMode()) {
            HaskellError.output(start,"unexpected expression");
        }
        this.push(this.fac.buildAList((HaskellExp) start,(HaskellExp)step,(HaskellExp)end));
    }

    @Override
    public void  inACompList(ACompList node){ this.pushMark();}
    @Override
    public void outACompList(ACompList node){
        List<HaskellObject> list = this.popMarkList();
        HaskellExp exp = (HaskellExp) list.remove(0);
        HaskellQual[] arr = new HaskellQual[list.size()];
        int i=0;
        for (HaskellObject ho : list){
           arr[i] = (HaskellQual)ho;
           i++;
        }
        this.push(this.fac.buildListComp(exp,arr));
    }

    @Override
    public void  inAFexp(AFexp node){ this.pushMark();}
    @Override
    public void outAFexp(AFexp node){ this.push(this.fac.buildApplies(this.popMarkList())); }

    @Override
    public void outAEmptylistGcon(AEmptylistGcon node){
        Token tok = node.getLopen();
        this.push(this.fac.buildCons(this.symfac.emptyListCons(tok)));
    }

    @Override
    public void outATupleGcon(ATupleGcon node){
        Token tok = node.getOpen();
        int i = node.getComma().size()+1;
        this.push(this.fac.buildCons(this.symfac.tuple(tok,i)));
    }

    @Override
    public void outAGenQual(AGenQual node){
        HaskellExp exp = (HaskellExp) this.pop();
        HaskellPat pat =(HaskellPat) this.pop();
        this.push(this.fac.buildGenQual(pat,exp));
    }

    @Override
    public void outAGuardQual(AGuardQual node){
       this.push(this.fac.buildExpQual((HaskellExp) this.pop()));
    }

    @Override
    public void  inALetQual(ALetQual node){ this.pushMark(); }
    @Override
    public void outALetQual(ALetQual node){
        Token tok = node.getKwlet();
        if (!this.isExpMode()) {
            HaskellError.output(tok,"unexpected expression");
        }
        List<HaskellDecl> list = new Vector<HaskellDecl>();
        for (HaskellObject ho : this.popMarkList()){
           list.add((HaskellDecl)ho);
        }
        this.push(this.fac.buildLetQual(list,tok));
    }


    @Override
    public void outAIdCon(AIdCon node)  { this.buildCons(); }
    @Override
    public void outAOpCon(AOpCon node)  { this.buildCons(); }
    @Override
    public void outAIdQcon(AIdQcon node){ this.buildCons(); }
    @Override
    public void outAOpQcon(AOpQcon node){ this.buildCons(); }
     public void buildCons(){
        this.push(this.fac.buildCons((HaskellSym) this.pop()));
     }

    @Override
    public void caseTKwinfix(TKwinfix node)       { this.curToken = node; this.fixity = InfixDecl.FIXITY_NON; }
    @Override
    public void caseTKwinfixl(TKwinfixl node)     { this.curToken = node; this.fixity = InfixDecl.FIXITY_LEFT; }
    @Override
    public void caseTKwinfixr(TKwinfixr node)     { this.curToken = node; this.fixity = InfixDecl.FIXITY_RIGHT; }
    @Override
    public void caseTConid(TConid node)           { this.buildSym(node); }
    @Override
    public void caseTQqconid(TQqconid node)       { this.buildSym(node); }
    @Override
    public void caseTConsym(TConsym node)         { this.buildSym(node); }
    @Override
    public void caseTQqconsym(TQqconsym node)     { this.buildSym(node); }
    @Override
    public void caseTVarid(TVarid node)           { this.buildSym(node); }
    @Override
    public void caseTQqvarid(TQqvarid node)       { this.buildSym(node); }
    @Override
    public void caseTVarsympre(TVarsympre node)   { this.buildSym(node); }
    @Override
    public void caseTQqvarsym(TQqvarsym node)     { this.buildSym(node); }
    @Override
    public void outAMinusVarsym(AMinusVarsym node){ this.buildSym(node.getMinus()); }
    @Override
    public void outAExclaVarsym(AExclaVarsym node){ this.buildSym(node.getExcla()); }
    public void buildSym(Token node) { this.push(this.symfac.createSym(node)); }
    public void buildSymQ(Token node) { this.push(this.symfac.createSym(node)); }

    @Override
    public void outAIdVar(AIdVar node)  { this.buildVar(); }
    @Override
    public void outAOpVar(AOpVar node)  { this.buildVar(); }
    @Override
    public void outAIdQvar(AIdQvar node){ this.buildVar(); }
    @Override
    public void outAOpQvar(AOpQvar node){ this.buildVar(); }
     public void buildVar(){
        this.push(this.fac.buildVar((HaskellSym) this.pop()));
     }

    @Override
    public void outAVarOp(AVarOp node)       { this.buildVOp(); }
    @Override
    public void outAConOp(AConOp node)       { this.buildCOp(); }
    @Override
    public void outAQvarQop(AQvarQop node)   { this.buildVOp(); }
    @Override
    public void outAQconQop(AQconQop node)   { this.buildCOp(); }
    @Override
    public void outAQvarQopm(AQvarQopm node) { this.buildVOp(); }
    @Override
    public void outAQconQopm(AQconQopm node) { this.buildCOp(); }
     public void buildVOp(){
        this.push(this.fac.buildOperator((Var)this.fac.buildVar((HaskellSym)this.pop())));
     }
     public void buildCOp(){
        this.push(this.fac.buildOperator((Cons)this.fac.buildCons((HaskellSym)this.pop())));
     }

    @Override
    public void outAKwasconid(AKwasconid node){
        HaskellSym co=  (HaskellSym) this.pop();
        HaskellSym as = (HaskellSym) this.pop();
        if (!(as.getName(false).equals("as"))) {
            HaskellError.output(as,"as expected");
        }
        this.push(co);
    }

    @Override
    public void  inAImpdecl(AImpdecl node){
    }

    @Override
    public void outAImpdecl(AImpdecl node){
        ImpSpec impSpec = null;
        HaskellSym alias = null;
        if(node.getImpspec() != null){impSpec = (ImpSpec) this.pop();}
        if(node.getKwasconid() != null){ alias = (HaskellSym) this.pop();}
        HaskellSym module = (HaskellSym) this.pop();
        this.imps.add((ImpDecl)this.fac.buildImpDecl(node.getKwimport(),node.getKwqualified(),module,alias,impSpec));

        boolean isPrelude = module.getName(false).equals("Prelude");

        if (!isPrelude && Options.isWebInterfaceMode) {
            HaskellError.output(node.getKwimport(), "imports other than Prelude are not allowed in the web-interface");
        }
    }

    @Override
    public void outAEmptyImpspec(AEmptyImpspec node){
        this.push(this.fac.buildImpSpec(node.getKwhiding(),node.getOpen(),new Vector<HaskellImport>()));
    }

    @Override
    public void inASomeImpspec(ASomeImpspec node){ this.pushMark();}
    @Override
    public void outASomeImpspec(ASomeImpspec node){
        List<HaskellImport> list = new Vector<HaskellImport>();
        for (HaskellObject ho : this.popMarkList()){
           list.add((HaskellImport)ho);
        }
        this.push(this.fac.buildImpSpec(node.getKwhiding(),node.getOpen(),list));
    }

    @Override
    public void outAConImport(AConImport node){
        if(node.getQcnames() == null) {
            Cons cons = (Cons) this.peek();
            cons.setTYPE();
        } else {
            this.push(this.fac.buildConsImport((Cons)this.pop(),this.exImpConsAtoms));
        }
    }

    @Override
    public void outAConExport(AConExport node){
        if(node.getQcnames() == null) {
            Cons cons = (Cons) this.peek();
            cons.setTYPE();
        } else {
            this.push(this.fac.buildConsExport((Cons)this.pop(),this.exImpConsAtoms));
        }
    }

    @Override
    public void outAModuleExport(AModuleExport node){
        this.push(this.fac.buildModExport(node.getKwmodule(),(HaskellSym) this.pop()));
    }

    @Override
    public void outAEmptyQcnames(AEmptyQcnames node){ this.exImpConsAtoms = new Vector<Atom>(); }
    @Override
    public void outAAllQcnames(AAllQcnames node) { this.exImpConsAtoms = null;}
    @Override
    public void inASomeQcnames(ASomeQcnames node){ this.pushMark();}
    @Override
    public void outASomeQcnames(ASomeQcnames node){
        this.exImpConsAtoms = new Vector<Atom>();
        for (HaskellObject ho : this.popMarkList()){
           Atom a = (Atom) ho;
           a.setQCNAME();
           this.exImpConsAtoms.add(a);
        }
    }

    @Override
    public void inAFuncDecl(AFuncDecl node){ this.pushMode(ASTBuilder.PAT); }
    @Override
    public void outAFuncDecl(AFuncDecl node) { this.popMode(); }

    @Override
    public void inADirectRhs(ADirectRhs node){ //System.err.println("inADirectRHS");
    this.pushMode(ASTBuilder.EXP); }
    @Override
    public void outADirectRhs(ADirectRhs node){
        this.popMode();
        //System.err.println("outADirectRHS");
        WhereDecls wdecs = null;
        if(node.getWheredecls() != null) { wdecs = (WhereDecls) this.pop();}
        HaskellExp exp = (HaskellExp) this.pop();
        RawTerm lhs = (RawTerm) this.pop();
        this.push(this.fac.buildFuncDecl(lhs,exp,wdecs));
    }

    @Override
    public void inACondsRhs(ACondsRhs node){ this.pushMark(); this.pushMode(ASTBuilder.EXP); }
    @Override
    public void outACondsRhs(ACondsRhs node){
        this.popMode();
        WhereDecls wdecs = null;
        if(node.getWheredecls() != null) { wdecs = (WhereDecls) this.pop();}
        List<CondExp> list = new Vector<CondExp>();
        for (HaskellObject ge : this.popMarkList()){
           list.add((CondExp)ge);
        }
        RawTerm lhs = (RawTerm) this.pop();
        this.push(this.fac.buildFuncDecl(lhs,list,wdecs));
    }

    @Override
    public void  inAFixityDecl(AFixityDecl node){ this.pushMark(); }
    @Override
    public void outAFixityDecl(AFixityDecl node){
        List<HaskellObject> objs = this.popMarkList();
        int priority = InfixDecl.PRIORITY_DEFAULT;
        if(node.getInteger() != null){
            IntegerLit prio = (IntegerLit) objs.remove(0);
            priority = prio.getIntValue();
        }
        node.getFixity().apply(this);
        List<Operator> list = new Vector<Operator>();
        for (HaskellObject ho : objs){
            list.add((Operator)ho);
        }
        this.push(this.fac.buildInfixDecl(this.curToken,this.fixity,priority,list));
    }

    @Override
    public void inAWheredecls(AWheredecls node){ this.pushMark(); }
    @Override
    public void outAWheredecls(AWheredecls node){
        Token tok = node.getKwwhere();
        List<HaskellDecl> list = new Vector<HaskellDecl>();
        for (HaskellObject ho : this.popMarkList()){
           list.add((HaskellDecl)ho);
        }
        this.push(this.fac.buildWhereDecls(tok,list));
    }

    @Override
    public void outAGdrhs(AGdrhs node){
        HaskellExp exp = (HaskellExp) this.pop();
        HaskellExp guard = (HaskellExp) this.pop();
        this.push(this.fac.buildCondExp(guard,exp));
    }

    @Override
    public void outAEmptyExports(AEmptyExports node){ this.expList = new Vector<HaskellExport>(); }
    @Override
    public void inASomeExports(ASomeExports node){ this.pushMark();}
    @Override
    public void outASomeExports(ASomeExports node){
        this.expList = new Vector<HaskellExport>();
        for (HaskellObject ho : this.popMarkList()){
           this.expList.add((HaskellExport)ho);
        }
    }

    @Override
    public void outAOneModules(AOneModules node){
        Module m = (Module) this.pop();
        if (this.isMain) {
           m.setMainModule();
        }
        this.modules.addModuleAndBuildImpMap(m);
    }


    @Override
    public void inASomeModules(ASomeModules node){
        if (Options.isWebInterfaceMode) {
            HaskellError.output(node.getKwmainmodule(), "modules are not allowed in the web-interface");
        }
        this.pushMark();
    }
    @Override
    public void outASomeModules(ASomeModules node){
        Token tok = node.getKwmainmodule();
        List<Module> list = new Vector<Module>();
        List<HaskellObject> objs = this.popMarkList();
        HaskellSym name = (HaskellSym) objs.remove(0);
        String namestr = name.getName(false);
        boolean mainfound = false;
        for (HaskellObject ho : objs){
            Module m = (Module) ho;
            if (namestr.equals(m.getName())) {
                m.setMainModule();
                mainfound = true;
            }
            this.modules.addModuleAndBuildImpMap(m);
        }
        if (!mainfound) {
            HaskellError.output(tok,"Main module "+namestr+" not found");
        }
        if (this.modules.needMoreModules()){
            Set<String> names = this.modules.getNamesOfNeededModules();
            HaskellError.output(tok,"Module set incomplete, missing modules: "+names);
        }
    }

    @Override
    public void inAUnnamedOnemodule(AUnnamedOnemodule node){
        this.pushMark();
        this.imps = new Vector<ImpDecl>();
    }
    @Override
    public void outAUnnamedOnemodule(AUnnamedOnemodule node){
        //this.expList = new Vector<HaskellExport>();
        this.expList = null;
        // TODO ??? an unnamed module can have imports, too
//        this.imps = new Vector<ImpDecl>();
        List<HaskellDecl> list = new Vector<HaskellDecl>();
        for (HaskellObject ho : this.popMarkList()){
           list.add((HaskellDecl)ho);
        }
        Token tok = null;
        if (list.size() > 0) {
            tok = list.get(0).getToken();
        }
        this.push(this.fac.buildModule(tok,this.symfac.newHaskellNamedSym("Main"),this.expList,this.imps,list));
    }

    @Override
    public void inAModule(AModule node){
        if (Options.isWebInterfaceMode) {
            HaskellError.output(node.getKwmodule(), "modules are not allowed in the web-interface");
        }
        this.pushMark();
        this.imps = new Vector<ImpDecl>();
        this.expList = null;
        //new Vector<HaskellExport>();
    }
    @Override
    public void outAModule(AModule node){
        Token tok = node.getKwmodule();
        List<HaskellDecl> list = new Vector<HaskellDecl>();
        List<HaskellObject> objs = this.popMarkList();
        HaskellSym name = (HaskellSym) objs.remove(0);
        for (HaskellObject ho : objs){
           list.add((HaskellDecl)ho);
        }
        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            System.err.println(tok);
        }

        HaskellObject ho = this.fac.buildModule(tok,name,this.expList,this.imps,list);
        this.push(ho);

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            System.err.println(ho.getToken()+",  "+tok);
        }
    }

    @Override
    public void inATermsModules(ATermsModules node){
        this.pushMark();
    }

    @Override
    public void inATerm(ATerm node){  this.pushMark(); }
    @Override
    public void outATerm(ATerm node){
        HaskellExp exp = (HaskellExp) this.pop();
        List<HaskellObject> objs = this.popMarkList();
        List<Var> vars = new Vector<Var>();
        for (HaskellObject ho : objs){
           vars.add((Var)ho);
        }
        Token tok = node.getKwterm();
        this.push(this.fac.buildStartTerm(tok,vars,exp));
    }

    @Override
    public void inAFbindsAexp1(AFbindsAexp1 node){ this.pushMark(); }
    @Override
    public void outAFbindsAexp1(AFbindsAexp1 node){
        List<FieldEqu> list = new Vector<FieldEqu>();
        List<HaskellObject> objs = this.popMarkList();
        HaskellObject obj = objs.remove(0);
        for (HaskellObject ho : objs){
           list.add((FieldEqu)ho);
        }
        this.push(this.fac.buildLabeled(obj,list));

    }

    @Override
    public void outAFbind(AFbind node){
        HaskellExp exp = (HaskellExp) this.pop();
        Var var = (Var) this.pop();
        var.setFBIND();
        this.push(this.fac.buildFieldEqu(var,exp));
    }

    public HaskellExp getTerm(){
        return (HaskellExp) this.pop();
    }

    public List<HaskellExp> getTerms(){
        List<HaskellObject> objs = this.popMarkList();
        List<HaskellExp> exps = new Vector<HaskellExp>();
        for (Object obj : objs){
            exps.add((HaskellExp)obj);
        }
        return exps;
    }

    @Override
    public void outASatype(ASatype node){
        if(node.getExcla() != null){
            this.push(this.fac.buildExcla(node.getExcla(),this.pop()));
        }
    }

    @Override
    public void outAFuncGtycon(AFuncGtycon node){
        this.push(this.fac.buildCons(this.symfac.arrowCons(node.getRarrow())));
    }

    @Override
    public void outAVarAtype(AVarAtype node){
        ((Var) this.peek()).setTYPE();
    }

    @Override
    public void outAConAtype(AConAtype node){
        ((Cons)this.peek()).setTYCONS();
    }

    @Override
    public void outAListAtype(AListAtype node){
        Cons cons = (Cons) this.fac.buildCons(this.symfac.emptyListCons(node.getLopen()));
        cons.setTYCONS();
        this.push(this.fac.buildApply(cons,this.pop()));
    }

    @Override
    public void outAEmptyTypetuple(AEmptyTypetuple node){
        Cons cons = (Cons) this.fac.buildCons(this.symfac.typeTuple(node.getOpen(),0));
        cons.setTYPE();
        this.push(cons);
    }

    @Override
    public void inASomeTypetuple(ASomeTypetuple node){ this.pushMark(); }
    @Override
    public void outASomeTypetuple(ASomeTypetuple node){
        List<HaskellObject>tups = this.popMarkList();
        if (tups.size() == 1) {
          this.push(tups.get(0));
        } else {
          Cons cons = (Cons) this.fac.buildCons(this.symfac.typeTuple(node.getOpen(),tups.size()));
          cons.setTYPE();
          tups.add(0,cons);
          this.push(this.fac.buildApplies(tups));
        }
    }

    @Override
    public void inABtype(ABtype node){ this.pushMark(); }
    @Override
    public void outABtype(ABtype node){
        this.push(this.fac.buildApplies(this.popMarkList()));
    }

    @Override
    public void inAType(AType node){ this.pushMark(); }
    @Override
    public void outAType(AType node){
        int m = this.popMarkCount()-1;
        HaskellObject cur = this.pop();
        for (int i=0;i<m;i++){
            cur = this.fac.buildArrow(this.pop(),cur);
        }
        this.push(cur);
    }

    @Override
    public void outACtype(ACtype node){
        HaskellObject matrix = this.pop();
        Context context = new Context();
        context.setToken(matrix.getToken());
        if(node.getContext() != null){
             context = (Context) this.pop();
        }
        this.push(this.fac.buildType(context,matrix));
    }

    @Override
    public void inASigDecl(ASigDecl node){ this.pushMark(); }
    @Override
    public void outASigDecl(ASigDecl node) {
        List<Var> vars = new Vector<Var>();
        HaskellPreType type = (HaskellPreType) this.pop();
        for (HaskellObject ho : this.popMarkList()){
           vars.add((Var)ho);
        }
        this.push(this.fac.buildTypeDecl(vars,type));
    }

    @Override
    public void outAExpDecl(AExpDecl node){
        RawTerm rt = (RawTerm) this.pop();
        this.push(rt.toTypeDecl());
    }

    @Override
    public void outAPrefixConstr(APrefixConstr node){
        this.push(this.fac.buildDataCon(this.pop()));
    }

    @Override
    public void outAPrefixNewconstr(APrefixNewconstr node){
        HaskellObject atype = this.pop();
        HaskellObject con = this.pop();
        this.push(this.fac.buildDataCon(con,atype));
    }


    @Override
    public void outAInfixConstr(AInfixConstr node){
        HaskellObject right = this.pop();
        HaskellSym op = (HaskellSym) this.pop();
        HaskellObject left = this.pop();
        this.push(this.fac.buildDataCon(op,left,right));
    }

    @Override
    public void outAContext(AContext node){
        this.push(this.fac.buildContext(this.pop()));
    }

    @Override
    public void inAFieldConstr(AFieldConstr node) { this.pushMark(); }
    @Override
    public void outAFieldConstr(AFieldConstr node) {
        List<HaskellObject> objs = this.popMarkList();
        Cons constr = (Cons) objs.remove(0);

        List<Var> fields = new LinkedList<Var>();
        List<HaskellObject> types = new LinkedList<HaskellObject>();
        List<Boolean> strictness = new LinkedList<Boolean>();
        for (HaskellObject ho : objs) {
            FieldDecl fdecl = (FieldDecl) ho;
            fields.add(fdecl.getField());
            types.add(fdecl.getType());
            strictness.add(fdecl.getStrict());
        }
        DataCon dataCon = (DataCon) this.fac.buildDataCon(constr.getSymbol(), types, fields);
        dataCon.setStrictness(strictness);
        this.push(dataCon);
    }

    @Override
    public void inAFielddecl(AFielddecl node) {  }
    @Override
    public void outAFielddecl(AFielddecl node) {
        HaskellObject obj = this.pop();
        HaskellExp type;
        boolean isStrict = false;
        if (obj instanceof StrictnessFlag) {
            type = (HaskellExp) ((StrictnessFlag)obj).getType();
            isStrict = true;
        }
        else {
            type = (HaskellExp) obj;
        }
        Var var = (Var) this.pop();
        this.push(this.fac.buildFieldDecl(var,isStrict, type));
    }

    @Override
    public void inADataTopdecl(ADataTopdecl node){ this.pushMark(); }
    @Override
    public void outADataTopdecl(ADataTopdecl node){
        Derivings derivings = null;
        if(node.getDeriving() != null){
            derivings = (Derivings) this.pop();
        }
        List<DataCon> dataCons = new Vector<DataCon>();
        List<HaskellObject> objs = this.popMarkList();
        Context context = null;
        if(node.getContext() != null){
             context = (Context) objs.remove(0);
        }
        HaskellObject defType = objs.remove(0);
        for (HaskellObject ho : objs){
           dataCons.add((DataCon)ho);
        }
        this.push(this.fac.buildDataDecl(node.getKwdata(),context,defType,dataCons,false,derivings));

        for (DataCon con : dataCons) {
            int pos=0;
            if (con.getFields() != null) {
                for (Var field : con.getFields()) {
                    this.push(this.fac.buildFieldSelectorFunction(field,pos++,con));
                }
            }
        }
    }

    @Override
    public void inANewtypeTopdecl(ANewtypeTopdecl node){  this.pushMark(); }
    @Override
    public void outANewtypeTopdecl(ANewtypeTopdecl node){
        Derivings derivings = null;
        if(node.getDeriving() != null){
            derivings = (Derivings) this.pop();
        }
        List<DataCon> dataCons = new Vector<DataCon>();
        List<HaskellObject> objs = this.popMarkList();
        Context context = null;
        if(node.getContext() != null){
             context = (Context) objs.remove(0);
        }
        HaskellObject defType = objs.remove(0);
        for (HaskellObject ho : objs){
           dataCons.add((DataCon)ho);
        }
        this.push(this.fac.buildDataDecl(node.getKwnewtype(),context,defType,dataCons,true,derivings));
    }

    @Override
    public void inAClassTopdecl(AClassTopdecl node){  this.pushMark(); }
    @Override
    public void outAClassTopdecl(AClassTopdecl node) {
        List<HaskellDecl> iClassDecls = new Vector<HaskellDecl>();
        List<HaskellObject> objs = this.popMarkList();
        Context context = null;
        if(node.getContext() != null){
             context = (Context) objs.remove(0);
        }
        HaskellObject defType = objs.remove(0);
        for (HaskellObject ho : objs){
           iClassDecls.add((HaskellDecl)ho);
        }
        this.push(this.fac.buildClassDecl(node.getKwclass(),context,defType,iClassDecls));
    }

    @Override
    public void inAInstanceTopdecl(AInstanceTopdecl node){  this.pushMark(); }
    @Override
    public void outAInstanceTopdecl(AInstanceTopdecl node){
        List<HaskellDecl> iInstDecls = new Vector<HaskellDecl>();
        List<HaskellObject> objs = this.popMarkList();
        Context context = null;
        if(node.getContext() != null){
             context = (Context) objs.remove(0);
        }
        HaskellObject defType = objs.remove(0);
        for (HaskellObject ho : objs){
           iInstDecls.add((HaskellDecl)ho);
        }
        this.push(this.fac.buildInstDecl(node.getKwinstance(),context,defType,iInstDecls));
    }

    @Override
    public void outADefaultTopdecl(ADefaultTopdecl node){
        this.push(this.fac.buildDefaultDecl(node.getKwdefault(),this.pop()));
    }

    @Override
    public void outATypeTopdecl(ATypeTopdecl node){
        HaskellObject type = this.pop();
        HaskellObject defType = this.pop();
        this.push(this.fac.buildSynTypeDecl(node.getKwtype(),defType,type));
    }

    @Override
    public void outAOneDeriving(AOneDeriving node){
        List <Cons> deris= new Vector<Cons>();
        Cons co = (Cons) this.fac.buildCons((HaskellSym)this.pop());
        co.setTYCLASS();
        deris.add(co);
        this.push(this.fac.buildDerivings(node.getKwderiving(),deris));
    }

    @Override
    public void inASomeDeriving(ASomeDeriving node){ this.pushMark(); }
    @Override
    public void outASomeDeriving(ASomeDeriving node){
        List <Cons> deris = new Vector<Cons>();
        for (HaskellObject ho : this.popMarkList()){
           Cons co = (Cons) this.fac.buildCons((HaskellSym)ho);
           co.setTYCLASS();
           deris.add(co);
        }
        this.push(this.fac.buildDerivings(node.getKwderiving(),deris));
    }

}
