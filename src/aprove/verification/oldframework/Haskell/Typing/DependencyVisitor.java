package aprove.verification.oldframework.Haskell.Typing;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Modules.Module;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * @author Stephan Swiderski
 *
 * This visitor collects the dependencies between the entities of an HaskellObject
 * and stores them into an Graph.
 */

public abstract class DependencyVisitor extends HaskellVisitor {
    public Set<HaskellEntity> visited;
    public HaskellDepGraph depGraph;
    public Stack<HaskellEntity> entityStack;
    private final Set<HaskellEntity.Sort> filter;

    public DependencyVisitor(final Set<HaskellEntity.Sort> filter) {
        this.entityStack = new Stack<HaskellEntity>();
        this.entityStack.push(null);
        this.depGraph = new HaskellDepGraph();
        this.visited = new HashSet<HaskellEntity>();
        this.filter = filter;
    }

    public HaskellDepGraph getDepGraph() {
        return this.depGraph;
    }

    public List<Set<HaskellEntity>> buildGroups() {
        final List<Set<HaskellEntity>> res = new Vector<Set<HaskellEntity>>();
        final List<Cycle<HaskellEntity>> cys = (new SCCGraph(this.depGraph)).getRankedSCCs();
        for (final Cycle<HaskellEntity> cy : cys) {
            final Set<HaskellEntity> group = cy.getNodeObjects();
            this.groupModuleCheck(group);
            res.add(group);
        }
        return res;
    }

    public void groupModuleCheck(final Set<HaskellEntity> group) {
        Module mod = null;
        for (final HaskellEntity e : group) {
            if (e.getModule() != mod) {
                if (mod == null) {
                    mod = e.getModule();
                } else {
                    HaskellError.output(e.getValue(), "Type declarations depends mutual intermodular");
                }
            }
        }
    }

    @Override
    public void fcaseEntity(final HaskellEntity e) {
        this.entityStack.push(e);
    }

    @Override
    public HaskellObject caseEntity(final HaskellEntity e) {
        this.entityStack.pop();
        return e;
    }

    @Override
    public boolean guardEntity(final HaskellEntity ho) {
        if (this.filter.contains(ho.getSort())) {
            if (ho.getModule().isAccessible()) {
                if (!this.visited.contains(ho)) {
                    this.visited.add(ho);
                    return true;
                }
            }
        }
        return false;
    }

}
