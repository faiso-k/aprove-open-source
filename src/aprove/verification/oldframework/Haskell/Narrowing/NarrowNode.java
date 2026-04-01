package aprove.verification.oldframework.Haskell.Narrowing;

import java.util.*;

import org.json.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Modules.Module;
import aprove.verification.oldframework.Haskell.Substitutors.*;
import aprove.verification.oldframework.Haskell.Typing.*;
import aprove.verification.oldframework.Utility.*;

public class NarrowNode implements BasicTermIndex.Carrier<NarrowNode> {

    static int count = 0;

    /**
     * @param from From node.
     * @param to To node.
     * @param label Edge label.
     * @return A JSONObject representing an edge between the specified nodes with the specified label.
     */
    private static JSONObject toJSONEdge(NarrowNode from, NarrowNode to, Object label) {
        JSONObject res = new JSONObject();
        res.put("from", from.getNum());
        res.put("to", to.getNum());
        if (label != null) {
            res.put("label", label);
        }
        return res;
    }

    Annotation annotation;

    BasicTermIndex<NarrowNode> basicTermIndex;

    List<NarrowNode> children;

    Set<ClassConstraint> constraints;

    HaskellExp expression;

    Set<NarrowNode> instNodes;

    boolean linkable;

    Object mark;

    int num;

    Object tag;

    String term;

    private int evalSubtermID;

    public NarrowNode(
        HaskellExp expression,
        Set<ClassConstraint> constraints,
        Annotation annotation,
        boolean linkable,
        boolean rootable
    ) {
        this.setExpression(expression);
        this.setConstraints(constraints);
        this.setAnnotation(annotation);
        this.linkable = linkable;
        this.instNodes = null;
        if (rootable) {
            this.setRootable();
        }
        this.tag = null;
        this.num = NarrowNode.count;
        NarrowNode.count++;
        this.evalSubtermID = -1;
    }

    public void addInstNode(NarrowNode instNode) {
        this.instNodes.add(instNode);
    }

    public Annotation getAnnotation() {
        return this.annotation;
    }

    @Override
    public BasicTermIndex<NarrowNode> getBasicTermIndex() {
        return this.basicTermIndex;
    }

    public List<NarrowNode> getChildren() {
        return this.children;
    }

    public Set<ClassConstraint> getConstraints() {
        return this.constraints;
    }

    public int getEvalSubtermID() {
        return this.evalSubtermID;
    }

    public HaskellExp getExpression() {
        return this.expression;
    }

    public Set<NarrowNode> getInstNodes() {
        return this.instNodes;
    }

    public Object getMark() {
        return this.mark;
    }

    public Mode getMode() {
        if (this.annotation == null) {
            return Mode.NON;
        }
        return this.annotation.getMode();
    }

    public int getNum() {
        return this.num;
    }

    public Object getTag() {
        return this.tag;
    }

    public boolean isLinkable() {
        return this.linkable;
    }

    public boolean isRoot() {
        return (this.instNodes != null) && (this.instNodes.size()>0);
    }

    public boolean isRootable() {
        return this.instNodes != null;
    }

    public void removeInstNode(NarrowNode instNode) {
        this.instNodes.remove(instNode);
    }

    public void resetLinkable() {
        this.linkable = false;
    }

    public void resetRootable(){
        if ( (this.instNodes != null) && (!this.instNodes.isEmpty()) ) {
            throw new RuntimeException("there are instances!");
        }
        this.instNodes = null;
    }

    public void setAnnotation(Annotation annotation) {
        this.annotation = annotation;
    }

    @Override
    public void setBasicTermIndex(BasicTermIndex<NarrowNode> basicTermIndex) {
        this.basicTermIndex = basicTermIndex;
    }

    public void setChildren(List<NarrowNode> children) {
        this.children = children;
    }

    public void setConstraints(Set<ClassConstraint> constraints) {
        this.constraints = constraints;
    }

    public void setEvalSubtermID(int evalSubtermID) {
        this.evalSubtermID = evalSubtermID;
    }

    public void setExpression(HaskellExp expression) {
        if (expression != null) {
            HaskellNarrowing.test(expression);
        }
        this.term = expression+"";
        this.expression = Copy.deep(expression);
    }

    public void setInstNodes(Set<NarrowNode> instNodes) {
        this.instNodes = instNodes;
    }

    public void setLinkable() {
        this.linkable = true;
    }

    public void setMark(Object mark) {
        this.mark = mark;
    }

    public void setRootable() {
        this.instNodes = new HashSet<NarrowNode>();
    }

    public void setTag(Object tag) {
        this.tag = tag;
    }

    public String toDOTLabel(Module module) {
        String w="";
        TyVarNameGenerator tvng=new TyVarNameGenerator();
        for (ClassConstraint cs : this.getConstraints()){
            HaskellType typ = (HaskellType)(Copy.deep(cs.getType())).visit(new AutoNameVarSubstitutor(tvng,module));
            w = w + "  " + cs.getTyClass() + " " + (new PLAIN_Util()).haskellObject(typ,module);
        }
        HaskellType type = Copy.deep(this.getExpression().getTypeTerm());
        type = (HaskellType)type.visit(new AutoNameVarSubstitutor(tvng,module));
        //return this.toString()+"\\n"+this.getExpression().toString(); //+"\\n"+this.getConstraints().toString();
        //StringBuffer t = new StringBuffer();
        //this.getExpression().appendExport(9,new PLAIN_Util(),t);
        //return this.getExpression().toString(); //+"\\n"+this.getConstraints().toString();
        //HaskellNarrowing.test(this.getExpression());
        /*
        Collection<HaskellObject> col = new ArrayList<HaskellObject>();
        TypeAnnotationCollector tac = new TypeAnnotationCollector(col);
        this.getExpression().visit(tac);
        */
        String ww = (new PLAIN_Util()).haskellObject(this.getExpression(),module); //+"\\n"+
//                    +col;
//               (new PLAIN_Util()).haskellObject(type,module)+"\\n"+w;
        //HaskellNarrowing.test(this.getExpression());
        return ww;
    }

    /**
     * @param module The main Haskell module.
     * @return A JSONObject representing the Haskell graph rooted in this node.
     */
    public JSONObject toJSONObject(Module module) {
        JSONObject res = new JSONObject();
        res.put("type", "Haskell graph");
        JSONObject nodes = new JSONObject();
        nodes.put("type", "nodes");
        JSONArray edges = new JSONArray();
        Export_Util eu = new PLAIN_Util();
        Iterator<NarrowNode> it = new TreeIterator(this, true);
        while (it.hasNext()) {
            NarrowNode node = it.next();
            JSONObject jsonNode = new JSONObject();
            jsonNode.put("type", "node");
            jsonNode.put("root", node.isRoot());
            jsonNode.put("mode", node.getMode().toString());
            final Object nodeLabel;
            switch (node.getMode()) {
                case INSTANCE: {
                    InstanceAnnotation instanceAnnotation = (InstanceAnnotation)node.getAnnotation();
                    NarrowNode base = instanceAnnotation.getBase();
                    JSONArray instance = new JSONArray();
                    Iterator<NarrowNode> itn = node.getChildren().iterator();
                    for (Var var : instanceAnnotation.getVars()) {
                        JSONArray pair = new JSONArray();
                        pair.put(eu.haskellObject(var, module));
                        pair.put(eu.haskellObject(itn.next().getExpression(), module));
                        instance.put(pair);
                    }
                    nodeLabel = instance;
                    edges.put(NarrowNode.toJSONEdge(node, base, "BASE"));
                    for (NarrowNode child : node.getChildren()) {
                        edges.put(NarrowNode.toJSONEdge(node, child, "INSTANCE"));
                    }
                    break;
                }
                case TYCASE: {
                    nodeLabel = node.toDOTLabel(module);
                    TyCaseAnnotation ca = (TyCaseAnnotation)node.getAnnotation();
                    Iterator<HaskellType> tit = ca.getVarTypes().iterator();
                    for (NarrowNode child : node.getChildren()) {
                        HaskellType type = Copy.deep(tit.next());
                        type = (HaskellType)type.visit(new AutoNameVarSubstitutor(new TyVarNameGenerator(), module));
                        JSONArray label = new JSONArray();
                        label.put(eu.haskellObject(new Var(new HaskellNamedSym(ca.getVarEntity())), module));
                        label.put(eu.haskellObject(type, module));
                        edges.put(NarrowNode.toJSONEdge(node, child, label));
                    }
                    break;
                }
                case CASE: {
                    nodeLabel = node.toDOTLabel(module);
                    CaseAnnotation ca = (CaseAnnotation)node.getAnnotation();
                    Iterator<HaskellSubstitution> sit = ca.getSubstitutions().iterator();
                    for (NarrowNode child : node.getChildren()) {
                        edges.put(NarrowNode.toJSONEdge(node, child, sit.next().export(eu, module)));
                    }
                    break;
                }
                case FIRST: {
                    nodeLabel = null;
                    break;
                }
                default:
                    nodeLabel = node.toDOTLabel(module);
                    for (NarrowNode child : node.getChildren()) {
                        edges.put(NarrowNode.toJSONEdge(node, child, null));
                    }
                    break;
            }
            if (nodeLabel != null) {
                jsonNode.put("label", nodeLabel);
                nodes.put("" + node.getNum(), jsonNode);
            }
        }
        res.put("nodes", nodes);
        res.put("edges", edges);
        return res;
    }

    @Override
    public String toString() {
        String anno = " annull ";
        if (this.annotation != null) {
            anno = this.annotation.toString();
        }
        String childs = "";
        if (this.children == null){
            childs = " chnull ";
        } else {
            for (NarrowNode child : this.children){
                childs = childs + child.num + " ";
            }
        }
        return this.num + "{" + anno + "} " + childs + " = " + this.term;
    }

}
