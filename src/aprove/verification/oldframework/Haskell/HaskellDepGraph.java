package aprove.verification.oldframework.Haskell;

import java.util.*;

import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Utility.Graph.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * The HaskellDepGraph is a Graph of HaskellEntities with convenience.
 *
 */
public class HaskellDepGraph extends Graph<HaskellEntity,Object> {

   /**
    * constructor for an empty HaskellDepGraph
    */
   public HaskellDepGraph() {
        super();
   }

   /**
    * constructor for a HaskellDepGraph which is a subgraph of graph
    * with only the node for HaskellEntity occuring in graph and the set entities
    */
   public HaskellDepGraph(Set<HaskellEntity> entities, HaskellDepGraph graph) {
        super(graph.getNodesFromObjects(entities),graph);
   }

   /**
    * adds a new node for HaskellEntity e
    */
   public Node<HaskellEntity> addNode(HaskellEntity e){
        Node<HaskellEntity> oNode = this.getNodeFromObject(e);
        if (oNode == null) {
             oNode = new Node<HaskellEntity>(e);
             this.addNode(oNode);
        }
        return oNode;
   }

   /**
    * adds an Edge from start to end HaskellEntity
    */
   public void addEdge(HaskellEntity start,HaskellEntity end){
       Node<HaskellEntity> startN = this.addNode(start);
       Node<HaskellEntity> endN = this.addNode(end);
       this.addEdge(startN, endN);
   }

   /**
    * @returns true,iff a path exists from the start to end HaskellEntity
    */
   public boolean pathFromTo(HaskellEntity start,HaskellEntity end){
       Node<HaskellEntity> sNode = this.getNodeFromObject(start);
       if (sNode == null) {
        return false;
    }
       Node<HaskellEntity> eNode = this.getNodeFromObject(end);
       if (eNode == null) {
        return false;
    }
       return this.hasPath(sNode,eNode);
   }

   /**
    * @returns a set of HaskellEntities reachable by the HaskellEntity start
    */
   public Set<HaskellEntity> determineReachables(Set<HaskellEntity> start) {
        Set<Node<HaskellEntity>> reachableNodes= this.determineReachableNodes(this.getNodesFromObjects(start));
        Set<HaskellEntity> reachables = new HashSet<HaskellEntity>();
        for (Node<HaskellEntity> enode : reachableNodes){
             reachables.add(enode.getObject());
        }
        return reachables;
   }

   /**
    * @returns the list of groups (mutual recursive blocks) ordered by dependency
    *         first depends one non, last one could depend on all predecessors
    */
   public List<Group> buildGroups(){
       List<Group> res = new Vector<Group>();
       List<Cycle<HaskellEntity>> cys = (new SCCGraph(this)).getRankedSCCs();
       for (Cycle<HaskellEntity> cy : cys){
           res.add(new Group(cy.getNodeObjects()));
       }
       return res;
   }

   /**
    * spezial copy function, using a map to create the nodes of the copy
    * edge from eMap.get(A) -> eMap.get(B) is created in the copy if the edges A->B exists in the orginal
    * the node eMap.get(A) is created if the node A exists in the orginal
    * map is assumed to be bijective
    */
   public void entityCopy(HaskellDepGraph old,Map<HaskellObject,HaskellObject> eMap){
       for (HaskellEntity e : old.getNodeObjects()){
           this.addNode((HaskellEntity)eMap.get(e));
       }
       for (Edge<Object,HaskellEntity> edge : old.getEdges()){
           Node<HaskellEntity> s = edge.getStartNode();
           Node<HaskellEntity> e = edge.getEndNode();
           this.addEdge((HaskellEntity)eMap.get(s.getObject()),(HaskellEntity)eMap.get(e.getObject()));
       }
   }

}
