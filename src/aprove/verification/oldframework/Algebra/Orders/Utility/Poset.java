package aprove.verification.oldframework.Algebra.Orders.Utility ;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.Terms.Visitors.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;

/** Implementation of a Partially Ordered Set.
 *
 * @author      Stephan Falke
 * @version $Id$
 */

public class Poset<T> extends OrderedSet<T> implements Exportable {

    private int minimal;

    /* constructors */

    public Poset() {
        super();
    }

    private Poset(List<T> set) {
    this.set = new ArrayList<T>(set);
    this.size = this.set.size();
    this.relation = new boolean[this.size*this.size];
    for(int i=0; i<this.size*this.size; i++) {
        this.relation[i] = false;
    }
        this.minimal = -1;
    }

    /** Creates a new instance of <code>Poset</code>.
     * @param set   the set that should be partially ordered
     */
    static public <U> Poset<U> create(Collection<U> set) {
        return new Poset<U>(new ArrayList<U>(set));
    }

    /** Creates a new instance of <code>Poset</code>.
     */
    static public <U> Poset<U> create() {
        return new Poset<U>(new ArrayList<U>());
    }

    /** Returns a deep copy of this Object.
     */
    public Poset<T> deepcopy() {
    Poset<T> p = new Poset<T>(this.set);
    System.arraycopy(this.relation, 0, p.relation, 0, this.size*this.size);
        p.minimal = this.minimal;
    return p;
    }

    /** Add <code>l</code> > <code>r</code> to the poset
     */
    @Override
    public void setGreater(T l, T r) throws OrderedSetException {
    int indexL, indexR, index;

    indexL = this.set.indexOf(l);
    indexR = this.set.indexOf(r);
    index = indexL + this.size*indexR;

    if(this.relation[index]==false) {
        this.relation[index] = true;
        this.updateTransitiveClosure(indexL, indexR);
        }
    }

    @Override
    public void setEquivalent(T l, T r) throws OrderedSetException {
        throw new PosetException("Operation is not permitted on PoSet");
    }


    /** Set <code>o</code> as the minimal element of this poset, i.e.
     * <code>o</code> is smaller than all <code>r != o</code>.
     */
    public void setMinimal(T o) throws PosetException {
    int index = this.set.indexOf(o);
    this.minimal = index;
    for(int j=0; j<this.size; j++) {
        if(index!=j) {
        this.relation[j + this.size*index] = true;
        }
    }
    this.calculateTransitiveClosure();
    }

    /** Is <code>o</code> the minimal element?
     */
    public boolean isMinimal(T o) {
    return this.set.indexOf(o)==this.minimal;
    }

    /** extends the set of this poset to include newSet as well.
     */
    public Poset<T> extendSet(List<T> newSet) {
    List<T> newVector = new ArrayList<T>(this.set);
    newVector.addAll(newSet);
    int newSize = newVector.size();
    Poset<T> res = Poset.create(newVector);

    /* strict part */
    for(int i=0; i<this.size; i++) {
        for(int j=0; j<this.size; j++) {
        if(this.relation[i + this.size*j]) {
            res.relation[i + newSize*j] = true;
        }
        }
    }
    /* minimal element */
    res.minimal = this.minimal;
    if(res.minimal != -1) {
        int offset = res.minimal * newSize;
        for(int i=0; i<newSize; i++) {
        res.relation[i + offset] = true;
        }
        /* minimal element is not greater that itself */
        res.relation[res.minimal + offset] = false;
    }
    return res;
    }

   /** Returns a poset based on this poset but not including oldSet.
    */
    public Poset<T> collapseSet(List<T> oldSet) {
        List<T> newVector = new ArrayList<T>(this.set);
    newVector.removeAll(oldSet);
    int newSize = newVector.size();
    Poset<T> res = Poset.create(newVector);

    int mapping[] = new int[newSize];
    int count = 0;
    Iterator it = newVector.iterator();
    while (it.hasNext()) {
        Object neW = it.next();
        int position = this.set.indexOf(neW);
        if (position == this.minimal) {
                res.minimal = count;
        }
        mapping[count] = position;
        count = count+1;
    }

    /* strict part */
    for(int i=0; i<newSize; i++) {
            for(int j=0; j<newSize; j++) {
            if(this.relation[mapping[i] + this.size*mapping[j]]) {
            res.relation[i + newSize*j] = true;
        }
        }
    }

    return res;
    }


    /** Merges the poset represented by this object with the poset
     * <code>other</code> and returns a new poset.
     */
    public Poset<T> mergeSlow(Poset<T> other) throws PosetException {
        if (this.size == 0) {
            return other;
        } else if (other.size == 0) {
            return this;
        }
        if ((this.size == other.size) && (this.set.equals(other.set))) {
            return this.merge(other);
        }
        Set<T> set = new HashSet<T>(this.set);
        set.addAll(other.set);
        List<T> vSet = new ArrayList<T>(set);

        int[] thisInd = new int[this.size];
        int[] otherInd = new int[other.size];

        for(int i=0; i<this.size; i++) {
            thisInd[i] = vSet.indexOf(this.set.get(i));
        }

        for(int i=0; i<other.size; i++) {
            otherInd[i] = vSet.indexOf(other.set.get(i));
        }

        Poset<T> res = Poset.create(vSet);
        for (int i = 0; i < this.size; i++) {
            for (int j = 0; j < this.size; j++) {
                if (this.relation[i + this.size * j]) {
                    res.relation[thisInd[i] + res.size*thisInd[j]] = true;
                }
            }
        }
        for (int i = 0; i < other.size; i++) {
            for (int j = 0; j < other.size; j++) {
                if (other.relation[i + other.size * j ]) {
                    res.relation[otherInd[i] + res.size*otherInd[j]] = true;
                }
            }
        }
        if(this.minimal!=-1 && other.minimal!=-1 && thisInd[this.minimal]!=otherInd[other.minimal]) {
            throw new PosetException("Incompatible minimal elements in mergeSlow!");
        }

        res.minimal = -1;

        if(this.minimal!=-1) {
            res.minimal = thisInd[this.minimal];
        }
        else if(other.minimal != -1) {
            res.minimal = otherInd[other.minimal];
        }

        if(res.minimal!=-1) {
            for(int i=0; i<res.size; i++) {
                if(i!=res.minimal) {
                    res.relation[i + res.size*res.minimal] = true;
                }
            }
        }

        res.calculateTransitiveClosure();
        return res;
    }

    /** Merges the poset represented by this object with the poset
     * <code>other</code> and returns a new poset.
     */
    public Poset<T> merge(Poset<T> other) throws PosetException {
    if(this.size!=other.size) {
        throw new PosetException("Incompatible posets in merge");
    }
    Poset<T> res = Poset.create(this.set);
    for(int i=0; i<this.size*this.size; i++) {
        if(this.relation[i] || other.relation[i]) {
            res.relation[i] = true;
        }
    }
        if(this.minimal != -1) {
        res.minimal = this.minimal;
    }
    else {
        res.minimal = other.minimal;
    }
    res.calculateTransitiveClosure();
    return res;
    }

    /** Intersects the poset represented by this object with the poset
     * <code>other</code> and returns a new poset.
     */
    public Poset<T> intersect(Poset<T> other) throws PosetException {
    if(this.size!=other.size) {
        throw new PosetException("Incompatible posets in intersect");
    }
    Poset<T> res = Poset.create(this.set);
    for(int i=0; i<this.size*this.size; i++) {
        if(this.relation[i] && other.relation[i]) {
            res.relation[i] = true;
        }
    }
    if(this.minimal==other.minimal) {
        res.minimal = this.minimal;
    }
    res.calculateTransitiveClosure();
    return res;
    }

    /** Returns <code>true</code> if the poset represented by this object
     * is contained in the poset <code>other</code>, <code>false</code>
     * otherwise.
     * A poset <code>P</code> is contained in a poset <code>Q</code>
     * iff <code>f</code> > <code>g</code> in <code>P</code> implies
     * <code>f</code> > <code>g</code> in <code>Q</code> for all
     * <code>f</code>, <code>g</code>.
     */
    public boolean isContainedIn(Poset<T> other) throws PosetException {
    if(this.size!=other.size) {
        throw new PosetException("Incompatible posets in isContainedIn");
    }
    for(int i=0; i<this.size*this.size; i++) {
         if(this.relation[i] && !other.relation[i]) {
         return false;
        }
    }
    return true;
    }

    /** Returns <code>true</code> if this poset and the poset
     * <code>o</code> contain the same relation, <code>false</code>
     * otherwise.
     */
    @Override
    public boolean equals(Object o) {
        Poset other;
    try {
        other = (Poset)o;
    }
    catch(ClassCastException e) {
        return false;
    }
    if(this.size!=other.size) {
        return false;
    }
    else {
        for(int i=0; i<this.size*this.size; i++) {
            if(this.relation[i] != other.relation[i]) {
            return false;
            }
        }
        return true;
    }
    }

    /* l > r was added ==> update the transitive closure */
    private void updateTransitiveClosure(int l, int r) throws PosetException {
    for(int i=0; i<this.size; i++) {
        if(this.relation[i + this.size*l]) {
            /* elem_i > elem_l, so we have to add elem_i > elem_r */
            this.relation[i + this.size*r] = true;
        }
    }
    for(int i=0; i<this.size; i++) {
        if(this.relation[r + this.size*i]) {
            /* elem_r > elem_i, so we have to add elem_l > elem_i */
        this.relation[l + this.size*i] = true;
        }
    }

    for(int i=0; i<this.size; i++) {
        if(this.relation[i + this.size*l]) {
            for(int j=0; j<this.size; j++) {
            if(this.relation[r + this.size*j]) {
                /* elem_i > elem_l and elem_r > elem_j, so we have
             * to add elem_i > elem_j */
            this.relation[i + this.size*j] = true;
            }
        }
        }
    }
    this.cycleCheck();
    }

    private void calculateTransitiveClosure() throws PosetException {
    for(int y=0; y<this.size; y++) {
        for(int x=0; x<this.size; x++) {
        if(this.relation[x + this.size*y]) {
            for(int j=0; j<this.size; j++) {
            if(this.relation[y + this.size*j]) {
                this.relation[x + this.size*j] = true;
            }
            }
        }
        }
    }
    this.cycleCheck();
    }

    private void cycleCheck() throws PosetException {
    for(int i=0; i<this.size; i++) {
        if(this.relation[i + this.size*i]) {
        StringBuffer excep = new StringBuffer("Exception: ");
        excep.append(this.set.get(i));
        excep.append(" > ");
        excep.append(this.set.get(i));
        throw new PosetException(excep.toString());
        }
    }
    }


    @Override
    public String toHashString() {
        StringBuffer result = new StringBuffer();

        for(int i=0; i<this.size; i++) {
            result.append(this.set.get(i));
            result.append(" >");
            boolean delim = false;
            for(int j=0; j<this.size; j++) {
            if(this.relation[i + this.size*j]) {
                if(delim) {
                    result.append(", ");
                }
                else {
                result.append(" ");
                delim = true;
                }
                result.append(this.set.get(j));
            }
            }
            if(i<this.size-1) {
            result.append("\n");
            }
        }

        return result.toString();
    }

    /** Returns a string representation of this object.
     */
    @Override
    public String toString() {
        StringBuffer result = new StringBuffer();

        boolean trivial = true;
        Iterator i = this.topSort().iterator();
        while(i.hasNext()) {
            List chain = (List)i.next();
            if(chain.size() == 1) {
                Object o = chain.get(0);
                if (o instanceof List) {
                    if (((List)o).size() > 1) {
                        trivial = false;
                        result.append(o.toString()+"\n");
                    }
                }
            } else {
                trivial = false;
                Iterator j = chain.iterator();
                while(j.hasNext()) {
                    Object o = j.next();
                    if (o instanceof List && ((List)o).size() == 1) {
                        o = ((List)o).get(0);
                    }
                    result.append(o.toString());
                    if(j.hasNext()) {
                    result.append(" > ");
                    }
                    else {
                    result.append("\n");
                    }
                }
            }
        }
        if (trivial) {
            return "trivial\n";
        }

        return result.toString();
    }

    public boolean isTrivial() {
        Iterator i = this.topSort().iterator();
        while(i.hasNext()) {
            List chain = (List)i.next();
            if(chain.size() == 1) {
                Object o = chain.get(0);
                if (o instanceof List) {
                    if (((List)o).size() > 1) {
                        return false;
                    }
                }
            } else {
                return false;
            }
        }
        return true;
    }

    @Override
    public String export(Export_Util eu) {
        if (eu instanceof PLAIN_Util) {
            return this.toString();
        } else if (eu instanceof HTML_Util) {
            return this.toHTML();
        } else if (eu instanceof LaTeX_Util) {
            return this.toLaTeX();
        } else {
            return this.toString();
        }
    }

    /** Returns a HTML representation of this object.
     */
    public String toHTML() {
        StringBuffer result = new StringBuffer("<BLOCKQUOTE>\n");

        boolean trivial = true;
        for (List chain : this.topSort()) {
            if (chain.size() == 1) {
                Object o = chain.get(0);
                // if this chain denotes equality of 2 or more elements, output this
                if (o instanceof List && ((List)o).size() > 1) {
                    trivial = false;
                    result.append(ToHTMLVisitor.escape(o.toString())+"<BR>\n");
                }
            } else {
                trivial = false;
                Iterator j = chain.iterator();
                while(j.hasNext()) {
                    Object o = j.next();
                    if (o instanceof List && ((List)o).size() == 1) {
                        o = ((List)o).get(0);
                    }
                    result.append(ToHTMLVisitor.escape(o.toString()));
                    if(j.hasNext()) {
                    result.append(" &gt; ");
                    }
                    else {
                    result.append("<BR>\n");
                    }
                }
            }
        }
        if (trivial) {
            return "<BLOCKQUOTE>trivial</BLOCKQUOTE>\n";
        }
        result.append("</BLOCKQUOTE>\n");
        return result.toString();
    }

    @Override
    public String toDOT() {
        StringBuffer t = new StringBuffer("digraph poset_graph {\n\n    node [shape=oval, outthreshold=100, inthreshold=100];\n\n");
        for (int i = 0; i < this.size; i++) {
            Object o = this.set.get(i);
            if (o instanceof List && ((List)o).size() == 1) {
                o = ((List)o).get(0);
            }
        if(i == this.minimal) {
                t.append("    " + Integer.valueOf(i).toString()+" [label=\""+o.toString()+"\", fontsize=16, color=green];\n");
        }
        else {
                t.append("    " + Integer.valueOf(i).toString()+" [label=\""+o.toString()+"\", fontsize=16];\n");
        }
    }
    t.append("\n");
    for(int i = 0; i < this.size; i++) {
        StringBuffer tmp = new StringBuffer("    " + (Integer.valueOf(i).toString()+" -> { "));
        boolean hasSucc = false;
            for (int j = 0; j < this.size; j++) {
                if (this.relation[i+this.size*j]) {
                    boolean flag = true;
                    for (int k = 0; k < this.size; k++) {
                        if (this.relation[i+this.size*k] && this.relation[k+this.size*j]) {
                            flag = false;
                        }
                    }
                    if (flag) {
            hasSucc = true;
                        tmp.append(Integer.valueOf(j).toString()+" ");
                    }
                }
            }
            tmp.append("};\n");
        if(hasSucc) {
            t.append(tmp);
        }
        }

        return t.toString()+"\n}\n";
    }

    /** Returns the subposet of this poset induced by newSet.
     */
    public Poset<T> project(Collection<T> newSet) {
    List<T> newVector = new ArrayList<T>(this.set);
    newVector.retainAll(newSet);
    int newSize = newVector.size();
    Poset<T> res = Poset.create(newVector);

    int mapping[] = new int[newSize];
    int count = 0;
    Iterator it = newVector.iterator();
    while (it.hasNext()) {
        Object neW = it.next();
        int position = this.set.indexOf(neW);
        if (position == this.minimal) {
            res.minimal = count;
        }
        mapping[count] = position;
        count = count+1;
    }

    /* strict part */
        for(int i=0; i<newSize; i++) {
        for(int j=0; j<newSize; j++) {
            if(this.relation[mapping[i] + this.size*mapping[j]]) {
            res.relation[i + newSize*j] = true;
        }
        }
    }

    return res;
    }

    public String toLaTeX() {
        StringBuffer result = new StringBuffer("\\begin{eqnarray*}\n");

        boolean trivial = true;
        Iterator<List<T>> i = this.topSort().iterator();
        while(i.hasNext()) {
            List chain = i.next();
            if(chain.size() == 1) {
                Object o = chain.get(0);
                if (o instanceof List) {
                    if (((List)o).size() > 1) {
                        trivial = false;
                        result.append("&&\\mathsf{"+ToLaTeXVisitor.escape(o.toString())+"}\\\\\n");
                    }
                }
            } else {
                trivial = false;
                result.append("&&");
                Iterator j = chain.iterator();
                while(j.hasNext()) {
                    Object o = j.next();
                    if (o instanceof List && ((List)o).size() == 1) {
                        o = ((List)o).get(0);
                    }
                    result.append("\\mathsf{"+ToLaTeXVisitor.escape(o.toString())+"}");
                    if(j.hasNext()) {
                        result.append(" \\sqsupset ");
                    }
                    else {
                        result.append("\\\\\n");
                    }
                }
            }
        }
        if (trivial) {
            return "\\begin{center}trivial\\end{center}\n";
        }
        result.append("\\end{eqnarray*}\n");
        return result.toString();
    }

    public List<List<T>> topSort() {
        List<List<T>> res = new ArrayList<List<T>>();
        boolean max[] = new boolean[this.size];

        for(int i=0; i<this.size; i++) {
        max[i] = true;
        for(int j=0; j<this.size; j++) {
            if(this.relation[j + this.size*i]) {
            max[i] = false;
            }
        }
        }


        for(int i=0; i<this.size; i++) {
        if(max[i]) {
            res.addAll(this.getAllChains(i));
        }
        }

        return res;
    }

    private List<List<T>> getAllChains(int i) {
        List<List<T>> res = new ArrayList<List<T>>();
        T o = this.set.get(i);

        boolean metaflag = false;
        for(int j=0; j<this.size; j++) {
            if (this.relation[i+this.size*j]) {
                boolean flag = true;
                for (int k = 0; k < this.size; k++) {
                    if (this.relation[i+this.size*k] && this.relation[k+this.size*j]) {
                        flag = false;
                    }
                }
                if(flag) {
                    metaflag = true;
                    List<List<T>> tmpres = this.getAllChains(j);
                    Iterator<List<T>> l = tmpres.iterator();
                    while(l.hasNext()) {
                        List<T> vec = l.next();
                        vec.add(0,o);
                        res.add(vec);
                    }
                }
            }
        }
        if(!metaflag) {
            List<T> resi = new ArrayList<T>();
            resi.add(this.set.get(i));
            res.add(resi);
        }

        return res;
    }



    public static String toCodish(Poset<FunctionSymbol> that, FreshNameGenerator vars, FreshNameGenerator funcs) {
        List<List<String>> merge = new Vector<List<String>>();
        Graph<Integer,Object> g = new Graph<Integer,Object>();
        Node<Integer>[] nodes = new Node[that.size];
        for(int i = 0; i < that.size; i++) {
            nodes[i] = new Node<Integer>(Integer.valueOf(i));
            g.addNode(nodes[i]);
        }
        for(int i = 0; i < that.size; i++) {
            for (int j = 0; j < that.size; j++) {
                if (that.relation[i+that.size*j]) {
                    g.addEdge(nodes[i], nodes[j]);
                }
            }
        }
        for (Set<Node<Integer>> rankO : g.getRanks()) {
            Set<Node<Integer>> rank = rankO;
            if (rank.isEmpty()) {
                continue;
            }
            List<String> syms = new Vector<String>();
            for (Node<Integer> node : rank) {
                Integer i = node.getObject();
                String name = ((FunctionSymbol) that.set.get(i)).getName();
                syms.add(funcs.getFreshName(name, true));
            }
            merge.add(0,syms);
        }
        return merge.toString();
    }

    @Override
    public Map<T,Integer> getTopSortMap() {
        Set<Integer> visited = new LinkedHashSet<Integer>();
        List<Integer> list = new ArrayList<Integer>();

        for (int i = 0; i < this.size; i++) {
            if (!visited.contains(i)) {
                this.getTopSortMapVisit(i, visited, list);
            }
        }
        Map<T,Integer> map = new LinkedHashMap<T,Integer>();
        for (int i = 0; i < list.size(); i++) {
            map.put(this.set.get(list.get(i)), i);
        }
        if (Globals.useAssertions) {
            for (int i = 0; i < this.size; i++) {
                for (int j = 0; j < this.size; j++) {
                    if (this.relation[i+this.size*j]) {
                        assert map.get(this.set.get(i)) > map.get(this.set.get(j));
                    }
                }
            }
        }
        return map;
    }

    private void getTopSortMapVisit(int i, Set<Integer> visited, List<Integer> list) {
        for (int j = 0; j < this.size; j++) {
            if (this.relation[i+this.size*j] && !visited.contains(j)) {
                this.getTopSortMapVisit(j, visited, list);
            }
        }
        list.add(i);
        visited.add(i);
    }

}
