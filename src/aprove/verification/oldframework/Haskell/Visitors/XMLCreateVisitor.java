package aprove.verification.oldframework.Haskell.Visitors;

import java.util.*;

import javax.xml.parsers.*;

import org.w3c.dom.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Declarations.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Literals.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Modules.Module;
import aprove.verification.oldframework.Haskell.Patterns.*;
import aprove.verification.oldframework.Haskell.Syntax.*;
import aprove.verification.oldframework.Haskell.Typing.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.Nodes.*;

/**
* @author Stephan Swiderski
*/

public class XMLCreateVisitor extends HaskellVisitor {
    public static boolean typeanno = false;
    public static boolean numberId = false;

    boolean fullExport = false;
    boolean allowOperators = true;
    boolean operatorsAsNames = false;
    Stack<EntityFrame> curFrames;
    Stack<Stack<Node>> nodeStack;
    Stack<NameGenerator> nameGenStack;
    NameGenerator lastNameGen;
    TypeSchema lastTypeSchema;
    Document doc;
    List<Node> classes;
    List<Node> instances;
    List<Node> dataTypes;
    Set<HaskellEntity> notUnique;
    Set<HaskellEntity> unreachables;
    Set<HaskellEntity> doNotShow;

    boolean inInst;
    Prelude prelude;
    Module module;
    Modules modules;

    public XMLCreateVisitor(final Document doc) {
        this.inInst = false;
        this.notUnique = new HashSet<HaskellEntity>();
        this.curFrames = new Stack<EntityFrame>();
        this.nodeStack = new Stack<Stack<Node>>();
        this.nameGenStack = new Stack<NameGenerator>();
        this.classes = new Vector<Node>();
        this.instances = new Vector<Node>();
        this.dataTypes = new Vector<Node>();
        this.doc = doc;
        this.lastNameGen = null;
        this.lastTypeSchema = null;
    }

    public XMLCreateVisitor(
        final Document doc,
        final boolean fullExport,
        final boolean allowOperators,
        final boolean operatorsAsName)
    {
        this(doc);
        this.fullExport = fullExport;
        this.allowOperators = allowOperators;
        this.operatorsAsNames = operatorsAsName;
    }

    public void buildNotUniqueGroup(final Modules modules) {
        this.prelude = modules.getPrelude();
        this.doNotShow = new LinkedHashSet<HaskellEntity>();
        this.doNotShow.add(this.prelude.getBool());
        this.doNotShow.add(this.prelude.getList());
        this.doNotShow.add(this.prelude.getTypeArrow());
        //this.doNotShow.addAll(this.prelude.getPreDefTyCons());
        final EntityMap name2entity = new EntityMap();
        for (final Module m : modules.getModules()) {
            for (final HaskellEntity e : m.getLocalEntities()) {
                if (!(e instanceof IVarEntity)) {
                    final HaskellEntity found = name2entity.get(e.getName(), e.getSort());
                    if (found != null) {
                        this.notUnique.add(e);
                        this.notUnique.add(found);
                    } else {
                        name2entity.add(e);
                    }
                }
            }
        }
    }

    @Override
    public HaskellObject caseModule(final Module ho) {
        if (!ho.isPrelude() || this.fullExport) {
            this.module = ho;
            final List<Node> childs = new Vector<Node>();
            final List<Node> cs = new Vector<Node>();
            final List<Node> ds = new Vector<Node>();
            final List<Node> is = new Vector<Node>();
            final List<Node> ims = new Vector<Node>();
            this.stackPush();
            for (final HaskellEntity e : this.sortByName(ho.getTopEntities())) {
                if (!this.unreachables.contains(e)) {
                    if (!(e instanceof TySynEntity)) {
                        e.visit(this);
                        if (!e.getModule().isPrelude() || this.fullExport) {
                            ;
                            switch (e.getSort()) {
                            case TYCLASS:
                                cs.add(this.pop());
                                break;
                            case TYCONS:
                                if (!this.doNotShow.contains(e)) {
                                    ds.add(this.pop());
                                }
                                break;
                            case INST:
                                is.add(this.pop());
                                break;
                            }
                        }
                    }
                }
            }
            childs.add(this.createName(ho, true, false));

            for (final HaskellEntity e : this.sortByName(this.modules.getModules())) {
                final Module m = (Module) e;
                boolean showQualifiedModule = (m != ho); // no self imports
                if (m.isPrelude()) {
                    showQualifiedModule = false; // don't show Prelude...
                    for (final List<ImpDecl> impDecls : ho.getImpQualMap().values()) {
                        for (final ImpDecl impDecl : impDecls) {
                            if (impDecl.getModule().getName(false).equals(m.getName())) {
                                showQualifiedModule = true; // ...unless Prelude is qualified
                                break;
                            }
                        }
                    }
                }
                if (showQualifiedModule || this.fullExport) {
                    final List<Node> ichs = new Vector<Node>();
                    ichs.add(this.create(HaskellElement.Qualified));
                    ichs.add(this.createName(m, true, false));
                    ims.add(this.create(HaskellElement.Import, ichs));
                }
            }

            if (ims.size() > 0) {
                childs.add(this.create(HaskellElement.Imports, ims));
            }
            final List<Cons> dls = ho.getDefaultList();
            if (dls != null) {
                final List<Node> dlns = new Vector<Node>();
                for (final Cons dl : dls) {
                    dlns.add(this.createName(dl.getSymbol(), false, false));
                }
                childs.add(this.create(HaskellElement.Default, dlns));
            }
            if (ds.size() > 0) {
                childs.add(this.create(HaskellElement.DataTypes, ds));
            }
            if (cs.size() > 0) {
                childs.add(this.create(HaskellElement.HClasses, cs));
            }
            if (is.size() > 0) {
                childs.add(this.create(HaskellElement.Instances, is));
            }
            childs.addAll(this.stackPop());
            this.push(this.create(HaskellElement.Module, childs));
        }
        return ho;
    }

    public void forModules(final Modules modules) {
        this.modules = modules;
        this.unreachables = this.modules.getUnreachables();
        this.prelude = modules.getPrelude();
        modules.visit(this);
    }

    /*    public void forModules(Modules modules){
        Set<HaskellEntity> all = new HashSet<HaskellEntity>();
            for (Module m : modules.getModules()){
             all.addAll(m.getTopEntities());
        }
        for (HaskellEntity e : this.sortByName(all)){
                 if (!(e instanceof TySynEntity)) {
                    e.visit(this);
                    if (!e.getModule().isPrelude()) {;
                       switch (e.getSort()) {
                           case TYCLASS : this.classes.add(this.pop()); break;
                           case TYCONS : this.dataTypes.add(this.pop()); break;
                           case INST : this.instances.add(this.pop()); break;
                       }
                    }
                 }
            }
       }*/

    public static Document buildDOM(
        final Modules modules,
        final boolean fullExport,
        final boolean allowOperators,
        final boolean operatorsAsName)
    {
        Document doc;
        try {
            doc = DocumentBuilderFactory.newInstance().newDocumentBuilder().newDocument();
        }
        catch (ParserConfigurationException shouldNotHappen) {
            // There's not much we can do in this case...
            throw new RuntimeException(shouldNotHappen);
        }
        doc.appendChild(doc.createElement("HaskellProgram"));
        final XMLCreateVisitor xcv = new XMLCreateVisitor(doc, fullExport, allowOperators, operatorsAsName);
        final Element root = doc.getDocumentElement();
        xcv.buildNotUniqueGroup(modules);
        xcv.stackPush();
        xcv.stackPush();
        xcv.push(xcv.createName(modules.getName()));
        xcv.pushNameGen(new TyVarNameGenerator());
        xcv.module = modules.getMainModule();
        if (modules.getStartTerms() != null) {
            for (final Pair<HaskellObject, HaskellExp> typedTerm : modules.getStartTerms()) {
                final QuantorExp ho = (QuantorExp) typedTerm.getValue();
                ho.getResult().visit(xcv);
                final Node result = xcv.pop();
                //TypeSchema.create((HaskellType)typedTerm.getKey()).visit(xcv);
                typedTerm.getKey().visit(xcv);
                xcv.push(xcv.tw(ho, xcv.create(HaskellElement.TypeBinding, result, xcv.pop())));
                xcv.push(xcv.create(HaskellElement.StartTerm, xcv.pop()));
            }
        }
        root.appendChild(xcv.create(HaskellElement.MainModule, xcv.stackPop()));
        xcv.pushNameGen(new TyVarNameGenerator());
        xcv.forModules(modules);
        for (final Node node : xcv.stackPop()) {
            root.appendChild(node);
        }
        return doc;
    }

    /*    public static Document buildDOM(Modules modules) {
            DOMImplementation domImpl = new DOMImplementationImpl();
            Document doc = domImpl.createDocument(null,"HaskellProgram",null);
            XMLCreateVisitor xcv = new XMLCreateVisitor(doc);
            xcv.buildNotUniqueGroup(modules);
            Element root = doc.getDocumentElement();
        root.appendChild(xcv.createWithTC(HaskellElement.Module,modules.getName()));
            xcv.stackPush();
            xcv.forModules(modules);

            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                System.out.println(xcv.dataTypes);
            }

            root.appendChild(xcv.create(HaskellElement.DataTypes,xcv.dataTypes));
            root.appendChild(xcv.create(HaskellElement.HClasses,xcv.classes));
            root.appendChild(xcv.create(HaskellElement.Instances,xcv.instances));
            for(Node node : xcv.stackPop()){
                root.appendChild(node);
            }
        return doc;
        }*/

    /*    public static Document buildStartTermDOM(Modules modules) {
            DOMImplementation domImpl = new DOMImplementationImpl();
            Document doc = domImpl.createDocument(null,"StartTerms",null);
            XMLCreateVisitor xcv = new XMLCreateVisitor(doc);
            for (HaskellExp sterm : modules.getStartTerms()){
                sterm.visit(xcv);
                root.appendChild(this.pop());
            }
        return doc;
        }*/

    public Element tw(final Node elem) {
        return this.create(HaskellElement.Term, elem);
    }

    public Element tw(final HaskellObject ho, final Node elem) {
        final HaskellObject ht = ho.getTypeTerm();
        if (XMLCreateVisitor.typeanno) {
            if (ht != null) {
                this.walk(ht, this);
                return this.create(HaskellElement.Term, this.create(HaskellElement.TypeAnno, this.pop()), elem);
            }
        }
        return this.tw(elem);
    }

    public void setPixity(final Element elem, final HaskellSym sym) {
        final HaskellEntity e = sym.getEntity();
        if (e == null) {
            return;
        }
        if (!sym.getOperator()) {
            return;
        }
        HaskellElement.FixityAttribute.priority.setAttribute(elem, e.getPriority() + "");
        String value = null;
        switch (e.getFixity()) {
        case InfixDecl.FIXITY_MONO:
            value = HaskellElement.FixityAttribute.Value_Non;
            break;
        case InfixDecl.FIXITY_NON:
            value = HaskellElement.FixityAttribute.Value_Non;
            break;
        case InfixDecl.FIXITY_LEFT:
            value = HaskellElement.FixityAttribute.Value_Left;
            break;
        case InfixDecl.FIXITY_RIGHT:
            value = HaskellElement.FixityAttribute.Value_Right;
            break;
        default:
        }
        HaskellElement.FixityAttribute.infix.setAttribute(elem, value);
    }

    public Element createInfixDecl(final HaskellEntity e) {
        if (e.getFixity() == InfixDecl.FIXITY_DEFAULT) {
            return null;
        }
        final Element elem = this.create(HaskellElement.InfixDecl, this.createName(e, true, true));
        HaskellElement.FixityAttribute.priority.setAttribute(elem, e.getPriority() + "");
        String value = null;
        switch (e.getFixity()) {
        case InfixDecl.FIXITY_MONO:
            value = HaskellElement.FixityAttribute.Value_Non;
            break;
        case InfixDecl.FIXITY_NON:
            value = HaskellElement.FixityAttribute.Value_Non;
            break;
        case InfixDecl.FIXITY_LEFT:
            value = HaskellElement.FixityAttribute.Value_Left;
            break;
        case InfixDecl.FIXITY_RIGHT:
            value = HaskellElement.FixityAttribute.Value_Right;
            break;
        default:
        }
        HaskellElement.FixityAttribute.infix.setAttribute(elem, value);
        return elem;
    }

    public Element create(final HaskellElement elem, final List<Node> childs) {
        final Element node = elem.createElement(this.doc);
        for (final Node child : childs) {
            node.appendChild(child);
        }
        return node;
    }

    public Element create(final HaskellElement elem, final Node... childs) {
        final Element node = elem.createElement(this.doc);
        for (final Node child : childs) {
            node.appendChild(child);
        }
        return node;
    }

    public String getName(final HaskellSym sym, final boolean def) {
        if (!sym.isNamed()) {
            return this.nameGenStack.peek().getNameFor(sym);
        }
        if (sym.getTuple() > 0) {
            if (this.operatorsAsNames) {
                return "Tup" + sym.getTuple();
            }
            String name = "(";
            for (int i = 0; i < sym.getTuple(); i++) {
                name = name + ",";
            }
            name = name + ")";
            return name;
        }
        return this.getName(sym.getEntity(), def);
    }

    private boolean isOperator(final String name) {
        final int i = name.indexOf('.');
        char c;
        if (i >= 0) {
            if (name.length() > 1) {
                c = name.charAt(i + 1);
            } else {
                return true;
            }
        } else {
            c = name.charAt(0);
        }
        return !(Character.isLetter(c) || c == '_' || c == '[' || c == '(');

    }

    private String wantOp(final String name, final boolean op) {
        final boolean isOp = this.isOperator(name);
        if (op && !isOp) {
            return "`" + name + "`";
        }
        if (isOp && this.operatorsAsNames) {
            return this.prelude.correctName(name);
        }
        if (!op && isOp) {
            return "(" + name + ")";
        }
        return name;
    }

    public Element createName(final HaskellSym sym) {
        final String name = this.wantOp(this.getName(sym, false), sym.getOperator() && this.allowOperators);
        return this.createWithTC(HaskellElement.Name, name);
    }

    public Element createName(final String name) {
        return this.createWithTC(HaskellElement.Name, name);
    }

    public Element createName(final HaskellSym sym, final boolean def, final boolean op) {
        final String name = this.wantOp(this.getName(sym, def), op && this.allowOperators);
        return this.createWithTC(HaskellElement.Name, name);
    }

    /*private String highLow(String name,boolean upCase){
       String mm = name.substring(1);
       char c = name.charAt(0);
       c = upCase ? Character.toUpperCase(c) : Character.toLowerCase(c);
       return c+mm;
    }*/

    public String getName(final HaskellEntity entity, final boolean def) {
        assert (entity != null);
        final boolean local = (entity instanceof VarEntity) && (((VarEntity) entity).getLocal());
        String name = null;
        final boolean mm =
            this.notUnique.contains(entity)
                || ((entity.getModule() != this.module) && (entity.getModule() != this.prelude));
        String wop = "";
        if (entity instanceof HaskellEntity.HaskellEntitySkeleton) {
            if (XMLCreateVisitor.numberId) {
                wop = ((HaskellEntity.HaskellEntitySkeleton) entity).num + "";
            }
        }
        if (!def && mm && !local) {
            //boolean upCase = HaskellEntity.Sort.UPCASE.contains(entity.getSort());
            //    name = this.highLow(entity.getModule().getName(),upCase)+"_"+this.prelude.correctName(entity.getName());
            name = entity.getModule().getName() + "." + entity.getName() + wop;
        } else {
            name = entity.getName() + wop;
        }
        return name;
    }

    public Element createName(final HaskellEntity he, final boolean def, final boolean op) {
        return this.createWithTC(HaskellElement.Name, this.wantOp(this.getName(he, def), op));
    }

    public Element createName(final HaskellEntity he) {
        return this.createWithTC(HaskellElement.Name, this.getName(he, false));
    }

    public Element createWithTC(final HaskellElement helem, final String content) {
        final Element elem = helem.createElement(this.doc);
        elem.setTextContent(content);
        return elem;
    }

    public void push(final Node node) {
        this.nodeStack.peek().push(node);
    }

    public Node pop() {
        return this.nodeStack.peek().pop();
    }

    public void pushNameGen(final NameGenerator node) {
        this.lastNameGen = node;
        this.nameGenStack.push(node);
    }

    public void popNameGen() {
        this.nameGenStack.pop();
    }

    public void stackPush() {
        this.nodeStack.push(new Stack<Node>());
    }

    public Stack<Node> stackPop() {
        final Stack<Node> nodes = this.nodeStack.pop();
        return nodes;
    }

    @Override
    public void fcaseEntityFrame(final EntityFrame ho) {
        this.curFrames.push(ho);

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.println("CurFrame: "+ho);
        }
    }

    @Override
    public void icaseEntityFrame(final EntityFrame ho) {
        this.curFrames.pop();

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.println("LeaveCurFrame: "+ho);
        }
    }

    public boolean tupleCheck(final Apply apply) {
        if (this.operatorsAsNames) {
            return false;
        }
        final List<HaskellObject> tups = HaskellTools.applyFlatten(apply);
        final HaskellObject ho = tups.get(0);
        if (ho instanceof Cons) {
            final int j = ((Cons) ho).getSymbol().getTuple();
            if (j == (tups.size() - 1)) {
                tups.remove(0);
                this.stackPush();
                for (final HaskellObject te : tups) {
                    te.visit(this);
                }
                this.push(this.tw(apply, this.create(HaskellElement.Tuple, this.stackPop())));
                return true;
            }
        }
        return false;
    }

    @Override
    public boolean outerGuardApply(final Apply ho) {
        return !this.tupleCheck(ho);
    }

    @Override
    public void fcaseApply(final Apply apply) {
        this.stackPush();
    }

    @Override
    public HaskellObject caseApply(final Apply apply) {
        this.push(this.tw(apply, this.create(HaskellElement.Apply, this.stackPop())));
        return apply;
    }

    @Override
    public HaskellObject caseCons(final Cons cons) {
        Element elem = null;
        if (cons.getSymbol().getName(false).equals("[]")) {
            elem = this.create(HaskellElement.Cons, this.create(HaskellElement.List, new Vector<Node>()));
        } else if (cons.getSymbol().getTuple() == 0) {
            elem =
                this.create(
                    HaskellElement.Cons,
                    this.createWithTC(HaskellElement.Name, this.operatorsAsNames ? "Tup0" : "()"));
        } else if (cons.getSymbol().getEntity() == this.prelude.getTypeArrow()) {
            elem = this.create(HaskellElement.Cons, this.create(HaskellElement.Arrow, new Vector<Node>()));
        } else {
            elem = this.create(HaskellElement.Cons, this.createName(cons.getSymbol()));
        }
        this.setPixity(elem, cons.getSymbol());
        this.push(this.tw(cons, elem));
        return cons;
    }

    @Override
    public HaskellObject caseVar(final Var var) {
        final Element elem = this.create(HaskellElement.Var, this.createName(var.getSymbol()));
        this.setPixity(elem, var.getSymbol());
        this.push(this.tw(var, elem));
        return var;
    }

    @Override
    public HaskellObject caseBindPat(final BindPat ho) {
        final Node var = this.pop();
        final Node pat = this.pop();
        this.push(this.tw(ho, this.create(HaskellElement.BindPat, var.getFirstChild(), pat)));
        return ho;
    }

    @Override
    public HaskellObject caseIrrPat(final IrrPat ho) {
        final Node pat = this.pop();
        this.push(this.tw(ho, this.create(HaskellElement.IrrPat, pat)));
        return ho;
    }

    @Override
    public HaskellObject caseJokerPat(final JokerPat ho) {
        this.push(this.tw(ho, this.create(HaskellElement.JokerPat)));
        return ho;
    }

    @Override
    public HaskellObject casePlusPat(final PlusPat ho) {
        final Node inte = this.pop();
        final Node var = this.pop();
        this.push(this.tw(ho, this.create(HaskellElement.PlusPat, var, inte)));
        return ho;
    }

    @Override
    public void fcaseFunction(final Function ho) {
        this.stackPush();
    }

    @Override
    public HaskellObject caseFunction(final Function ho) {
        final List<Node> childs = this.stackPop();
        this.pushFunction(ho.getSymbol().getEntity(), childs);
        return ho;
    }

    public void pushFunction(final HaskellEntity e, List<Node> childs) {
        if (childs == null) {
            childs = new Vector<Node>();
        }
        childs.add(0, this.createName(e, true, false));
        if (!this.inInst) {
            final Element elem = this.createInfixDecl(e);
            if (elem != null) {
                this.push(elem);
            }
        }
        final HaskellObject ty = this.inInst ? null : e.getType();
        if (ty != null) {
            ty.visit(this);
            final Node type = this.pop();
            childs.add(1, type);
        }
        this.push(this.create(HaskellElement.Function, childs));
    }

    @Override
    public void fcaseHaskellRule(final HaskellRule ho) {
        this.stackPush();
    }

    @Override
    public HaskellObject caseHaskellRule(final HaskellRule ho) {
        final Node result = this.pop();
        final Node pats = this.create(HaskellElement.Pattern, this.stackPop());
        this.push(this.create(HaskellElement.Rule, pats, result));
        return ho;
    }

    @Override
    public void fcaseCaseExp(final CaseExp ho) {
        this.stackPush();
    }

    @Override
    public HaskellObject caseCaseExp(final CaseExp ho) {
        this.push(this.tw(ho, this.create(HaskellElement.Case, this.stackPop())));
        return ho;
    }

    @Override
    public void fcaseAltExp(final AltExp ho) {
        this.stackPush();
    }

    @Override
    public HaskellObject caseAltExp(final AltExp ho) {
        final Node result = this.pop();
        final Node pats = this.create(HaskellElement.Pattern, this.stackPop());
        this.push(this.create(HaskellElement.Alt, pats, result));
        return ho;
    }

    @Override
    public void fcaseLambdaExp(final LambdaExp ho) {
        this.stackPush();
    }

    @Override
    public HaskellObject caseLambdaExp(final LambdaExp ho) {
        final Node result = this.pop();
        final Node pats = this.create(HaskellElement.Pattern, this.stackPop());
        this.push(this.tw(ho, this.create(HaskellElement.Lambda, pats, result)));
        return ho;
    }

    @Override
    public void fcaseIfExp(final IfExp ho) {
        this.stackPush();
    }

    @Override
    public HaskellObject caseIfExp(final IfExp ho) {
        this.push(this.tw(ho, this.create(HaskellElement.If, this.stackPop())));
        return ho;
    }

    @Override
    public HaskellObject caseCharLit(final CharLit ho) {
        String text = ho.getCharValue() + "";
        if ((ho.getCharValue() <= ' ') || (ho.getCharValue() > '~')) {
            text = "\\" + ((int) ho.getCharValue());
        }
        this.push(this.tw(ho, this.createWithTC(HaskellElement.Char, text)));
        return ho;
    }

    @Override
    public HaskellObject caseFloatLit(final FloatLit ho) {
        this.push(this.tw(ho, this.createWithTC(HaskellElement.Float, "" + ho.getFloatValue())));
        return ho;
    }

    @Override
    public HaskellObject caseIntegerLit(final IntegerLit ho) {
        this.push(this.tw(ho, this.createWithTC(HaskellElement.Int, "" + ho.getIntValue())));
        return ho;
    }

    @Override
    public void fcaseLetExp(final LetExp ho) {
        this.stackPush();
        for (final HaskellEntity e : this.sortByName(ho.getEntityFrame().getCollectedEntities())) {
            e.visit(this);
        }
    }

    @Override
    public HaskellObject caseLetExp(final LetExp ho) {
        final Node result = this.pop();
        final Node locals = this.create(HaskellElement.Locals, this.stackPop());
        if (ho.getMode() == LetExp.LET) {
            this.push(this.tw(ho, this.create(HaskellElement.Let, locals, result)));
        } else {
            this.push(this.tw(ho, this.create(HaskellElement.Where, locals, result)));
        }
        return ho;
    }

    @Override
    public HaskellObject casePatDecl(final PatDecl ho) {
        final Node result = this.pop();
        final Node pat = this.create(HaskellElement.Pattern, this.pop());
        this.push(this.create(HaskellElement.PatDecl, pat, result));
        return ho;
    }

    @Override
    public HaskellObject caseTypeExp(final TypeExp ho) {
        final Node result = this.pop();
        (ho.getTypeSchema()).visit(this);
        this.push(this.tw(ho, this.create(HaskellElement.TypeBinding, this.pop(), result)));
        return ho;
    }

    @Override
    public HaskellObject caseCondExp(final CondExp ho) {
        final Node result = this.pop();
        final Node cond = this.create(HaskellElement.Guard, this.pop());
        this.push(this.create(HaskellElement.Condition, cond, result));
        return ho;
    }

    @Override
    public void fcaseCondStackExp(final CondStackExp ho) {
        this.stackPush();
    }

    @Override
    public HaskellObject caseCondStackExp(final CondStackExp ho) {
        this.push(this.create(HaskellElement.Conditions, this.stackPop()));
        return ho;
    }

    @Override
    public HaskellObject caseEntity(final HaskellEntity ho) {
        if (ho.getModule().isPrelude() && !this.fullExport) {
            return ho;
        }
        if (ho instanceof IVarEntity) {
            final HaskellObject value = ho.getValue();
            if (value != null) {
                value.visit(this);
            } else {

            }
        } else if (ho instanceof CVarEntity) {
            final HaskellObject value = ho.getValue();
            if (value != null) {
                value.visit(this);
            } else {
                this.pushFunction(ho, null);
            }
        } else if (ho instanceof VarEntity) {
            final HaskellObject value = ho.getValue();
            if (!((VarEntity) ho).isHidden()) {
                value.visit(this);
            } else {
            }
        } else if (ho instanceof TyConsEntity) {
            if (this.doNotShow.contains(ho)) {
                return ho;
            }
            this.stackPush();
            final TyConsEntity tce = (TyConsEntity) ho;
            if (ho.getValue() == null) {
                final List<HaskellType> types =
                    this.prelude.deArrow(((TypeSchema) tce.getConsList().get(0).getType()).getMatrix());
                TypeSchema.create(types.get(types.size() - 1)).visit(this);
            } else {
                ((DataDecl) ho.getValue()).getTypeSchema().visit(this);
            }
            this.pushNameGen(this.lastNameGen);
            for (final HaskellEntity he : (tce.getConsList())) {
                final Element elem = this.createInfixDecl(he);
                if (elem != null) {
                    this.push(elem);
                }
                he.visit(this);
            }
            this.popNameGen();
            if (ho.getValue() != null) {
                final Derivings des = ((DataDecl) ho.getValue()).getDerivings();
                if (des != null) {
                    this.stackPush();
                    for (final Cons cons : des.getClasses()) {
                        this.push(this.createName(cons.getSymbol()));
                    }
                    this.push(this.create(HaskellElement.Derivings, this.stackPop()));
                }
            }
            if (tce.getNewType()) {
                this.push(this.create(HaskellElement.NewType, this.stackPop()));
            } else {
                this.push(this.create(HaskellElement.DataType, this.stackPop()));
            }

        } else if (ho instanceof InstEntity) {
            this.stackPush();
            this.stackPush();
            this.pushNameGen(new TyVarNameGenerator());
            ((InstEntity) ho).getConstraintRule().visit(this);
            final Node newClass = this.pop();
            this.push(this.create(HaskellElement.Constraints, this.stackPop()));
            this.push(newClass);
            this.popNameGen();
            this.stackPush();
            this.inInst = true;
            for (final HaskellEntity he : this.sortByName(ho.getSubEntities())) {
                he.visit(this);
            }
            this.inInst = false;
            this.push(this.create(HaskellElement.Members, this.stackPop()));
            this.push(this.create(HaskellElement.Instance, this.stackPop()));
        } else if (ho instanceof TyClassEntity) {
            this.stackPush();
            this.push(this.createName(ho));
            this.stackPush();
            final ClassConstraintRule ccr = ((ClassDecl) ho.getValue()).getClassConstraintRule();
            final NameGenerator nameGen = new TyVarNameGenerator();
            nameGen.getNameFor(((Var) ccr.getPattern().getType()).getSymbol());
            this.pushNameGen(nameGen);
            ccr.visit(this);
            final Node newClass = this.pop();
            this.push(this.create(HaskellElement.Constraints, this.stackPop()));
            this.push(newClass);
            this.popNameGen();
            this.stackPush();
            for (final HaskellEntity he : this.sortByName(ho.getSubEntities())) {
                he.visit(this);
            }
            this.push(this.create(HaskellElement.Members, this.stackPop()));

            this.push(this.create(HaskellElement.HClass, this.stackPop()));
        } else if (ho instanceof ConsEntity) {
            this.stackPush();
            String name = this.getName(ho, true);
            boolean isInfix = this.isOperator(name);
            if (this.operatorsAsNames) {
                final int tup = ((ConsEntity) ho).getTuple();
                if (tup >= 0) {
                    isInfix = false;
                    name = "Tup" + tup;
                }
            }
            this.push(this.createWithTC(HaskellElement.Name, name));
            this.deArrowRename(((TypeSchema) ho.getType()), (DataCon) ho.getValue());
            final Element elem = this.create(HaskellElement.Constr, this.stackPop());
            HaskellElement.FixityAttribute.infix.setAttribute(elem, isInfix + "");
            this.push(elem);
        } else if (ho instanceof PatDeclEntity) {
            final HaskellObject value = ho.getValue();
            value.visit(this);
        }
        return ho;
    }

    private void deArrowRename(final TypeSchema ts, final DataCon dc) {
        final HaskellType orgtype = this.lastTypeSchema.getMatrix();
        final List<HaskellType> types = this.prelude.deArrow(ts.getMatrix());
        final HaskellType restype = types.remove(types.size() - 1);
        final HaskellSubstitution subs = BasicTerm.Tools.match(restype, orgtype);
        final List<Boolean> strictness = dc == null ? null : dc.getStrictness();
        int i = 0;
        for (final HaskellType type : types) {
            (subs.applyTo(type)).visit(this);
            Node elem = this.pop();
            if (strictness != null) {
                if (strictness.get(i)) {
                    elem = this.tw(this.create(HaskellElement.Strict, elem));
                }
            }
            this.push(this.create(HaskellElement.Type, elem));
            i++;
        }
    }

    @Override
    public void fcaseTypeSchema(final TypeSchema ho) {
        this.lastTypeSchema = ho;
        if (ho instanceof MemberTypeSchema) {
            final ClassConstraint cc = ((MemberTypeSchema) ho).getClassConstraint();
            final NameGenerator nameGen = new TyVarNameGenerator();
            nameGen.getNameFor(((Var) cc.getType()).getSymbol());
            this.pushNameGen(nameGen);
        } else {
            this.pushNameGen(new TyVarNameGenerator());
        }
        this.stackPush();
    }

    @Override
    public HaskellObject caseTypeSchema(final TypeSchema ho) {
        this.popNameGen();
        final Node type = this.pop();
        this
            .push(this.create(HaskellElement.TypeSchema, this.create(HaskellElement.Constraints, this.stackPop()), type));
        return ho;
    }

    @Override
    public HaskellObject caseClassConstraint(final ClassConstraint ho) {
        final Node result = this.pop();
        final Node className = this.createWithTC(HaskellElement.ClassName, this.getName(ho.getTyClass(), false));
        this.push(this.create(HaskellElement.Constraint, className, result));
        return ho;
    }

    @Override
    public HaskellObject caseQuantor(final Quantor ho) {
        for (final HaskellSym sym : ho) {
            this.push(this.create(HaskellElement.Var, this.createName(sym)));
        }
        return ho;
    }

    @Override
    public void fcaseQuantorExp(final QuantorExp ho) {
        this.pushNameGen(new TyVarNameGenerator());
    }

    @Override
    public HaskellObject caseQuantorExp(final QuantorExp ho) {
        final Node sterm = this.pop();
        this.stackPush();
        for (final Var var : ho.getVariables()) {
            this.push(this.create(HaskellElement.Var, this.createName(var.getSymbol())));
        }
        this.push(sterm);
        this.push(this.create(HaskellElement.StartTerm, this.stackPop()));
        this.popNameGen();
        return ho;
    }

    @Override
    public HaskellObject caseOperator(final Operator ho) {
        return ho;
    }

    @Override
    public HaskellObject caseRawTerm(final RawTerm ho) {
        return ho;
    }

    @Override
    public HaskellObject caseTypeDecl(final TypeDecl ho) {
        return ho;
    }

    @Override
    public HaskellObject caseFuncDecl(final FuncDecl ho) {
        return ho;
    }

    @Override
    public HaskellObject caseHaskellSym(final HaskellSym ho) {
        return ho;
    }

    @Override
    public HaskellObject caseHaskellNamedSym(final HaskellNamedSym ho) {
        return ho;
    }

    @Override
    public HaskellObject casePreFunction(final PreFunction ho) {
        return ho;
    }

    @Override
    public HaskellObject casePreType(final HaskellPreType ho) {
        return ho;
    }

    @Override
    public HaskellObject caseClassDecl(final ClassDecl ho) {
        return ho;
    }

    @Override
    public HaskellObject caseInstDecl(final InstDecl ho) {
        return ho;
    }

    @Override
    public HaskellObject caseDataDecl(final DataDecl ho) {
        return ho;
    }

    @Override
    public HaskellObject caseDataCon(final DataCon ho) {
        return ho;
    }

    @Override
    public HaskellObject caseSynTypeDecl(final SynTypeDecl ho) {
        return ho;
    }

    //    public HaskellObject casePatDeclValue(PatDeclValue ho) { return ho;}

    @Override
    public boolean guardQuantorExpVars(final QuantorExp ho) {
        return false;
    }

    @Override
    public boolean guardDefType(final SynTypeDecl ho) {
        return true;
    }

    @Override
    public boolean guardConss(final DataDecl ho) {
        return false;
    }

    @Override
    public boolean guardEntity(final HaskellEntity ho) {
        return true;
    }

    @Override
    public boolean guardEntities(final Module ho) {
        return false;
    }

    @Override
    public boolean guardValue(final HaskellEntity ho) {
        return false;
    }

    @Override
    public boolean guardType(final HaskellEntity ho) {
        return false;
    }

    @Override
    public boolean guardMember(final HaskellEntity ho) {
        return false;
    }

    @Override
    public boolean guardTypeTypeExp(final TypeExp ho) {
        return false;
    }

    @Override
    public boolean guardDecls(final TTDecl ho) {
        return false;
    }

    @Override
    public boolean guardArguments(final HaskellRule ho) {
        return true;
    }

    @Override
    public boolean guardLetFrame(final LetExp ho) {
        return false;
    }

    //public boolean guardPatDeclEntity(PatDeclValue ho) { return true; }
    @Override
    public boolean guardHaskellNamedSym(final HaskellNamedSym ho) {
        return false;
    }

    public Set<HaskellEntity> sortByName(final Set<? extends HaskellEntity> es) {
        final Set<HaskellEntity> res = new TreeSet<HaskellEntity>(new EntityComparator());
        res.addAll(es);
        return res;
    }
}
