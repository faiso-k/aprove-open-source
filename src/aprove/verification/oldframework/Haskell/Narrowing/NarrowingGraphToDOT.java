package aprove.verification.oldframework.Haskell.Narrowing;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Substitutors.*;
import aprove.verification.oldframework.Haskell.Typing.*;
import aprove.verification.oldframework.Utility.*;

/**
 * @author Stephan Swiderski
 * @version $Id$
 */
public class NarrowingGraphToDOT extends NarrowingGraphAnalyser {

    public NarrowingGraphToDOT(Modules modules, NarrowNode freeAppNode) {
        super(modules, freeAppNode);
    }

    public void addEdge(NarrowNode from, NarrowNode nn, String color, String style, int w, StringBuffer t) {
        Vector<NarrowNode> nns = new Vector<NarrowNode>();
        nns.add(nn);
        this.addEdges(from, nns, null, color, style, w, t);
    }

    public void addEdges(
        NarrowNode from,
        List<NarrowNode> nns,
        List<String> labels,
        String color,
        String style,
        int w,
        StringBuffer t
    ) {
        Iterator<String> it = null;
        String lab = "";
        if (labels != null) {
            it = labels.iterator();
        }
        if (nns == null) {
            return;
        }
        for (NarrowNode nn : nns) {
            t.append(from.num + " -> " + nn.num);
            if (it != null) {
                lab = it.next();
            }
            t.append("[label=\"" + lab + "\",style=\"" + style + "\", color=\"" + color + "\", weight=" + w + "];\n");
        }
    }

    public void addNode(NarrowNode n, String label, String style, StringBuffer t, int size) {
        t.append(n.num + "[label=\"" + label + "\",fontsize=" + size);
        if (style != null) {
            t.append("," + style);
        }
        t.append("];");
    }

    public String buildDOT(NarrowNode tree) {
        Export_Util eu = new PLAIN_Util();
        StringBuffer t = new StringBuffer("digraph dp_graph {\nnode [outthreshold=100, inthreshold=100];");
        Iterator<NarrowNode> it = new TreeIterator(tree, true);
        String col = "";
        String style = "";
        String lstyle = "";
        int fs = 16;
        while (it.hasNext()) {
            NarrowNode node = it.next();
            if (node.getChildren() == null) {
                // XXX DEBUG
                if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                    System.out.println("----------->" + node.num);
                }
            }
            //style = (node.isRoot()) ? " style = \"dashed\"" : "style =\"solid\"";
            style = (node.isRoot()) ? ",shape=\"triangle\"" : ",shape=\"box\"";
            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                //System.out.println("DOT Node:"+node.num);
            }
            String w = "";
            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                if (node.getTag() != null) {
                    if (((Tag)node.getTag()).getVarExpFreeAppPred()) {
                        w = "!!";
                    }
                }
            }
            lstyle = "solid";
            switch (node.getMode()) {
                case NON:
                    col = "black";
                    break;
                case INSTANCE: {
                    InstanceAnnotation instanceAnnotation = (InstanceAnnotation)node.getAnnotation();
                    NarrowNode base = instanceAnnotation.getBase();
                    //NarrowNode snode = new NarrowNode(null,null,null,true,true);
                    String subsString = "";
                    //List<String> labs = new Vector<String>();
                    Iterator<NarrowNode> itn = node.getChildren().iterator();
                    for (Var var : instanceAnnotation.getVars()) {
                        subsString =
                            subsString
                            + eu.haskellObject(var, this.module)
                            + "/"
                            + eu.haskellObject(itn.next().getExpression(), this.module)
                            + "\\n";
                    }
                    //this.addNode(snode,subsString,"color=\"magenta\"",t);
                    this.addEdge(node, base, "red", "dashed", 0, t);
                    //this.addEdge(node,snode,"magenta",3,t);
                    this.addNode(node, w + node.toDOTLabel(this.module), this.fdotpar("color", "magenta"), t, fs);
                    this.addEdges(node, node.getChildren(), null, "magenta", "dashed", 3, t);
                    col = null;
                    break;
                }
                case TYCASE: {
                    this.addNode(node, w + node.toDOTLabel(this.module), this.fdotpar("color", "blue") + style, t, fs);
                    TyCaseAnnotation ca = (TyCaseAnnotation)node.getAnnotation();
                    //Iterator<Substitution> sit = ca.getTySubstitutions().iterator();
                    Iterator<HaskellType> tit = ca.getVarTypes().iterator();
                    for (NarrowNode child : node.getChildren()) {
                        HaskellType type = Copy.deep(tit.next());
                        type =
                            (HaskellType)type.visit(new AutoNameVarSubstitutor(new TyVarNameGenerator(), this.module));
                        String subsString =
                            eu.haskellObject(new Var(new HaskellNamedSym(ca.getVarEntity())), this.module)
                            + " :: "
                            + eu.haskellObject(type, this.module);
                        NarrowNode snode = new NarrowNode(null, null, null, false, false);
                        this.addNode(
                            snode,
                            subsString,
                            this.fdotpar("color", "white")
                            + this.dotpar("style", "solid")
                            + this.dotpar("shape", "box"),
                            t,
                            10
                        );
                        this.addEdge(node, snode, "blue", "solid", 9, t);
                        this.addEdge(snode, child, "blue", "solid", 3, t);
                    }
                    col = null;
                    break;
                }
                case CASE: {
                    this.addNode(
                        node,
                        w + node.toDOTLabel(this.module),
                        this.fdotpar("color", "burlywood") + style,
                        t,
                        fs
                    );
                    CaseAnnotation ca = (CaseAnnotation)node.getAnnotation();
                    Iterator<HaskellSubstitution> sit = ca.getSubstitutions().iterator();
                    for (NarrowNode child : node.getChildren()) {
                        String subsString = sit.next().export(eu, this.module);
                        NarrowNode snode = new NarrowNode(null, null, null, false, false);
                        this.addNode(
                            snode,
                            subsString,
                            this.fdotpar("color", "white")
                            + this.dotpar("style", "solid")
                            + this.dotpar("shape", "box"),
                            t,
                            10
                        );
                        this.addEdge(node, snode, "burlywood", "solid", 9, t);
                        this.addEdge(snode, child, "burlywood", "solid", 3, t);
                    }
                    col = null;
                    break;
                }
                case CONS:
                    col = "green";
                    lstyle = "dashed";
                    break;
                case PROGERROR:
                    col = "red";
                    lstyle = "dashed";
                    break;
                case UNIVAR:
                    col = "green";
                    lstyle = "dashed";
                    break;
                case FIRST:
                    col = null;
                    break;
                case VAREXP:
                    col = "grey";
                    lstyle = "dashed";
                    /*                        VarExpAnnotation VarExpAnnotation = (VarExpAnnotation)node.getAnnotation();
                                            NarrowNode vebase = VarExpAnnotation.getBase();
                                            this.addEdge(node,vebase,"blue","solid",3,t);*/
                    //col = null;
                    break;
                default:
                    break;
            }
            if (col != null) {
                this.addNode(node, w + node.toDOTLabel(this.module), this.fdotpar("color", col) + style, t, fs);
                this.addEdges(node, node.getChildren(), null, col, lstyle, 3, t);
            }
        }
        t.append("}\n");
        String o = t.toString();
        // XXX DEBUG
        //        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
        //            System.out.println(o);
        /*            try {
                        FileWriter oo = new FileWriter("/tmp/tmp.dot");
                        oo.write(o);
                        oo.close();
                    } catch (Exception e){
                       throw new RuntimeException(e);
                    }*/
        //        }
        return o;
    }

    public String dotpar(String name, String value) {
        return "," + name + "=\"" + value + "\"";
    }

    public String fdotpar(String name, String value) {
        return name + "=\"" + value + "\"";
    }

    /*
    public void buildGMChild(GenMap gm, StringBuffer t) {
        this.addGMNode(gm.num, gm.toString(), null, t);
        List<Integer> li = new Vector<Integer>();
        for (GenEntry ge : gm.values()) {
            li.add(ge.num);
        }
        this.addGMEdges(gm.num, li, null, "black", 0, t);
        for (GenEntry ge : gm.values()) {
            buildGEChild(ge, t);
        }
    }

    public void buildGEChild(GenEntry ge, StringBuffer t) {
        this.addGMNode(ge.num, ge.toString(), null, t);
        List<Integer> li = new Vector<Integer>();
        for (GenMap gm : ge.params) {
            li.add(gm.num);
        }
        this.addGMEdges(ge.num, li, null, "red", 0, t);
        for (GenMap gm : ge.params) {
            buildGMChild(gm, t);
        }
    }

    public String buildGMDOT() {
        StringBuffer t = new StringBuffer("digraph dp_graph {\nnode [outthreshold=100, inthreshold=100];");
        this.buildGMChild(this.genMap, t);
        t.append("}\n");
        String o = t.toString();

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            System.out.println(o);
        }

        try {
            FileWriter oo = new FileWriter("/home/swiste/tmp2.dot");
            oo.write(o);
            oo.close();
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
        return o;
    }

    public void addGMNode(int n, String label, String style, StringBuffer t) {
        t.append(n + "[label=\"" + label + "\",fontsize=16");
        if (style != null) {
            t.append("," + style);
        }
        t.append("];");
    }
    */

    /*public void addGMEdge(NarrowNode from, NarrowNode nn,String color,int w,StringBuffer t){
         Vector<Integer> nns = new Vector<Integer>();
         nns.add(nn);
         this.addGMEdges(from,nns,null,color,w,t);
    } */

    /*
    public void addGMEdges(int from, List<Integer> nns,List<String> labels,String color,int w,StringBuffer t){
        Iterator<String> it = null;
        String lab = "";
        if (labels != null) it = labels.iterator();
        for (Integer nn : nns){
            t.append(from+" -> "+nn);
            if (it != null) {
                lab = it.next();
            }
            t.append("[label=\""+lab+"\",style=\"solid\", color=\""+color+"\", weight="+w+"];\n");
        }
    }
    */

}
