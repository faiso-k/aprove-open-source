package aprove.verification.oldframework.LemmaDatabase;

import java.io.*;
import java.util.*;

import aprove.*;
import aprove.input.Formulas.pl.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Exceptions.*;
import aprove.verification.oldframework.LemmaDatabase.Index.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Rewriting.FunctionSymbolGraph;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

public class LemmaDatabase {

    protected long nextprimaryKey;

    /**
     * Formulas contained in this database
     */
    protected Set<Formula> formulas;

    /**
     * Implications contained in lemma database
     */
    protected Set<Implication> implications;

    /**
     * Equations contained in lemma database
     */
    protected Set<Equation> equations;

    /**
     * Lemma database change listeners
     */
    protected Vector<LemmaDatabaseUpdateListener> listeners;

    /**
     * Current program
     */
    protected Program program;

    /**
     *
     */
    protected Map<Formula,LemmaDatabaseEntry> lemmaDatabaseEntries;

    /**
     *
     */
    protected Map<Long,BasicObligationNode> unsavedProofs;

    /**
     * All the proofs which are marked for deletion.
     * They will not be saved during the next safe
     */
    protected List<Long> proofsMarkedForDeletion;

    protected IndexNode root;

    /**
     * Standard constructor
     */
    public LemmaDatabase() {
        this.nextprimaryKey             = 1;
        this.root                      = new IndexNode(null,null);
        this.formulas                  = new LinkedHashSet<Formula>();
        this.listeners                 = new Vector<LemmaDatabaseUpdateListener>();
        this.implications               = new LinkedHashSet<Implication>();
        this.equations                 = new LinkedHashSet<Equation>();
        this.lemmaDatabaseEntries      = new LinkedHashMap<Formula,LemmaDatabaseEntry>();
        this.unsavedProofs             = new LinkedHashMap<Long,BasicObligationNode>();
        this.proofsMarkedForDeletion = new Vector<Long>();
    }

    /**
     * Adds a formula to the index tree
     * @param formula Formula to add
     * @param basicObligationNode the proof of the formula
     */
    public synchronized void insert(Formula formula, BasicObligationNode basicObligationNode) {
        this.insert(formula, basicObligationNode,true);
    }

    /**
     *
     */
    protected synchronized void insert(Formula formula,
                                        BasicObligationNode basicObligationNode,
                                        boolean buildLemmaDatabaseEntry) {

        boolean reallyInserted = false;

        // Check if formula is implication or a equation
        if(formula.isImplication()) {
            this.implications.add((Implication)formula);
        }

        if(formula.isEquation()) {
            this.equations.add((Equation)formula);
        }

        // check if there exists already generalisation of the given formula
        Set<Formula> generalisations = this.retrieveGeneralisations(formula);

        if(!generalisations.isEmpty()) {
            return;
        }

        // create a lemma database entry for formula
        if( buildLemmaDatabaseEntry) {
            LemmaDatabaseEntry lemmaDatabaseEntry = this.buildLemmaDatabaseEntry(formula);
            this.lemmaDatabaseEntries.put(formula, lemmaDatabaseEntry);
            this.unsavedProofs.put(lemmaDatabaseEntry.getPrimaryKey(), basicObligationNode);
        }

        // add formula to the set of indexed formulas
        reallyInserted = this.formulas.add(formula);

        // set start node to the root of the index tree
        IndexNode   node = this.root;

        // get representation string for the given formula
        List<IndexSymbol> symbols = formula.getRepresentationString();

        // search the index tree for leaf corresponding to the given
        // formula. If there doesn't exist such a path a one
        Set<Formula> instances = new LinkedHashSet<Formula>();

        for(IndexSymbol symbol : symbols) {

            if(symbol.equals(new IndexVariableSymbol())) {
                instances.addAll(this.getAllInstances(formula,node.getReachableFormulas()));
            }

            if(node.containsKey(symbol)) {

                node.addReachableFormula(formula);
                node = node.get(symbol);

            }else{

                node.addReachableFormula(formula);

                IndexNode newNode = new  IndexNode(symbol,node);


                node.put(symbol,newNode);
                node = newNode;
            }

        }

        // add formula to the search results of this leaf
        node.addResult(formula);

        // notify all database listeners that the index contains a new formula
        // if there has been a real changement
        if (reallyInserted) {
            this.notifyAllLemmaDatabaseChangeListeners(LemmaDatabaseUpdateListener.Type.ADD, formula);
        }

        // remove all instances
        if(!instances.isEmpty()) {
            this.delete(instances);
        }
    }

    /**
     * Adds a collection of formulas to the index
     * @param formulas Formulas to add
     */
    public synchronized void insert(Collection<Pair<Formula,BasicObligationNode>> formulas) {
        for(Pair<Formula,BasicObligationNode> pair : formulas) {
            this.insert(pair.x, pair.y);
        }
    }

    /**
     * Returns all generalisations of the given formula contained in the
     * index tree.
     * @param query Formula for which the generalisations should be found
     * @return All generalisations found
     */
    public synchronized Set<Formula> retrieveGeneralisations(Formula query) {
        return this.retrieveGeneralisations(this.root, query, Position.create());
    }

    public synchronized Set<Formula> retrieveGeneralisations(Collection<Formula> queries) {
        Set<Formula> returnValue = new LinkedHashSet<Formula>();
        for(Formula query : queries) {
            returnValue.addAll(this.retrieveGeneralisations(query));
        }
        return returnValue;
    }

    /**
     * Method search all generalisations of the given formula based on the
     * current index node and the current position in the formula
     * @param node  Current index node
     * @param query Formula for wich the generalisations should be found
     * @param position Current position in the formula
     * @return All generalisations found
     */
    protected Set<Formula> retrieveGeneralisations(IndexNode node, Formula query, Position position) {

        // initialise return value
        Set<Formula> results = new LinkedHashSet<Formula>();

        try {

            // get the index symbol of the current subpart of the formula
            IndexSymbol rootSymbol = query.getSubPart(position).getRootIndexSymbol();

            // if the node is a leaf, add the formulas contained
            // to the return value.
            if(node.isLeaf()) {
                return node.getResults();
            }

            // Does the current index node contain the index symbol?
            if(node.containsKey(rootSymbol)) {

                // get the next index node to check
                IndexNode newNode = node.get(rootSymbol);

                Position nextPosition = this.next(query,position);
                results.addAll( this.retrieveGeneralisations(newNode,query,nextPosition));

            }

            // If current node does not contain the index symbol, check if the current index node
            // contains a variable symbol
            IndexVariableSymbol indexVariableSymbol = new IndexVariableSymbol();
            if( node.containsKey(indexVariableSymbol) ) {

                Position afterPosition = this.after(query,position);
                results.addAll( this.retrieveGeneralisations(node.get(indexVariableSymbol), query, afterPosition));

            }

        } catch (InvalidPositionException e) {
            // This should not happen. If it still happends there is an error
            // in the algorithm
            e.printStackTrace();
        }

        // check which formulas found by the index tree match the
        // query. This should be done because the given discrimination tree
        // is indeterministic.
        results.retainAll(this.filterAllGeneralisations(query,results));

        // return all results which were found and match the query
        return results;
    }

    /**
     * Calculates the position which should be visited after position, in a depth-first
     * left to right traversal.
     * @param termOrFormula Term or formula for which the next
     *           position should be calculated-
     * @param position Current position
     * @return Next position
     */
    protected Position next(TermOrFormula termOrFormula, Position position) {

        try {

            // get the arguments of the subpart addressed by position
            TermOrFormula subPart = termOrFormula.getSubPart(position);
            List<? extends TermOrFormula> arguments = subPart.getArguments();

            // Of a leaf is reached use the position return by after.
            // Othwerwise dive into depth in a left to right style.
            if( arguments==null || arguments.isEmpty() ) {
                return this.after(termOrFormula,position);
            }else{
                return position.shallowcopy().add(0);
            }

        } catch (InvalidPositionException e) {
            // This should not happen otherwise there is an error in
            // the algorithm.
            e.printStackTrace();
            return null;
        }
    }

    /**
     * Calculates the next position which should be visited in depth-first
     * left to right traversal if the whole subtree represented by position
     * is already visited.
     * @param termOrFormula Term or formula for which the position should be calculated
     * @param position Current position
     * @return New position
     */
    protected Position after(TermOrFormula termOrFormula, Position position) {

        try {

            // for epsilon return epsilon
            if (position.isEmpty()) {
                return position;
            }

            // get predecessor of this position and the last component
            // of this position
            int last = position.getLast();
            Position pred = position.pred();

            // check if there exists a subtree which was not visited yet.
            // Otherwise search recursivly using the predecessor
            if (termOrFormula.getSubPart(pred).getArguments().size() > last + 1) {
                return pred.shallowcopy().add(last+1);
            } else {
                return this.after(termOrFormula, pred);
            }

        } catch (InvalidPositionException e) {
            // This should not happen otherwise there is an error in
            // the algorithm.
            e.printStackTrace();
            return null;
        }

    }

    /**
     * Removes a collection of formulas from the index tree
     * @param formulas Collection of formulas to remove
     */
    public synchronized void delete(Collection<Formula> formulas) {
        for(Formula formula : formulas) {
            this.delete(formula);
        }
    }

    /**
     * Deletes a formula from the index tree
     * @param formula Formula to delete
     */
    public synchronized void delete(Formula formula) {

        // check if formula is an implication or an equation
        if(formula.isImplication()) {
            this.implications.remove(formula);
        }

        if(formula.isEquation()) {
            this.equations.remove(formula);
        }

        // remove formula from the set of index formulas
        this.formulas.remove(formula);

        // remember proof to be deleted
        this.proofsMarkedForDeletion.add(this.lemmaDatabaseEntries.get(formula).primaryKey);

        // remove corresponding lemma database entry
        this.lemmaDatabaseEntries.remove(formula);

        // set initial search node to the root of the index tree
        IndexNode node     = this.root;

        // get representation string for the given formula
        List<IndexSymbol> symbols = formula.getRepresentationString();

        // search for the leaf which should contain the formula
        for(IndexSymbol symbol : symbols) {

            if(node.containsKey(symbol)) {

                // on the down to the node remove formula from
                // the set of reachable formulas
                node.removeReachableFormula(formula);

                node = node.get(symbol);

            }else{
                return;
            }

        }

        if(node.isLeaf()) {

            // check if leaf contains more than one formula. If so remove
            // the given one from the set of results. Otherwise remove the
            // whole subtree leading to this node.
            if(node.numberOfFormulas() > 1) {

                node.removeResult(formula);

            }else{

                while( (node.getParent() != null) && (node.getParent().numberOfChildren() == 1) ) {
                    node.getParent().remove(node.getParentKey());
                    node = node.getParent();
                }

            }

        }


        // notify all database change listerners that a formula was removed
        this.notifyAllLemmaDatabaseChangeListeners(LemmaDatabaseUpdateListener.Type.REMOVE, formula);
    }

    /**
     * Returns all formulas cotained in the index tree.
     */
    public synchronized Set<Formula> retrieveAllFormulas() {
        return new LinkedHashSet<Formula>(this.formulas);
    }

    /**
     * Deletes all formulas from the index tree
     */
    public synchronized void deleteAll() {
        this.nextprimaryKey             = 1;
        this.root                      = new IndexNode(null,null);
        this.formulas                = new LinkedHashSet<Formula>();
        this.lemmaDatabaseEntries    = new LinkedHashMap<Formula,LemmaDatabaseEntry>();
        this.implications             = new LinkedHashSet<Implication>();
        this.equations                 = new LinkedHashSet<Equation>();
        this.unsavedProofs             = new LinkedHashMap<Long,BasicObligationNode>();
        this.proofsMarkedForDeletion = new Vector<Long>();

        this.notifyAllLemmaDatabaseChangeListeners(LemmaDatabaseUpdateListener.Type.REMOVE_ALL, null);
    }

    /**
     * Method removes all formula from the set which are could not be
     * matched against the formula
     * @param formula  Formula against which should be matched
     * @param formulas Set which from formulas which could not be matched
     *        should be removed
     * @return all matchers found
     */
    protected Set<Formula> getAllInstances(Formula formula, Set<Formula> formulas) {

        Set<Formula> returnValue = new LinkedHashSet<Formula>(formulas);

        for(Formula possibleMatcher : formulas) {

            AlgebraSubstitution substitution = formula.matches(possibleMatcher);

            if(substitution == null) {
                returnValue.remove(possibleMatcher);
            }

        }

        return returnValue;
    }

    /**
     * Method removes all formula from the set which could not be
     * matched against the formula
     * @param formula  Formula against which should be matched
     * @param formulas Set which from formulas which could not be matched
     *        should be removed
     * @return all matchers found
     */
    protected Set<Formula> filterAllGeneralisations(Formula formula, Set<Formula> formulas) {

        Set<Formula> returnValue = new LinkedHashSet<Formula>(formulas);

        for(Formula possibleMatcher : formulas) {

            AlgebraSubstitution substitution = possibleMatcher.matches(formula);

            if(substitution == null) {
                returnValue.remove(possibleMatcher);
            }

        }

        return returnValue;
    }

    public long getNextPrimaryKey() {
        return this.nextprimaryKey++;
    }

    /**
     * Registers a lemma database change lister
     * @param listener Listener to register
     */
    public void addLemmaDatabaseListener(LemmaDatabaseUpdateListener listener) {
        this.listeners.add(listener);
    }

    /**
     * Unregister a lemma database change listener
     * @param listener Listener to unregister
     */
    public void removeLemmaDatabaseListener(LemmaDatabaseUpdateListener listener){
        this.listeners.remove(listener);
    }

    /**
     * Notifies all register lemma database change listeners, that something
     * has happend
     * @param type Type of change
     * @param termOrFormula Term or Formula responsible for the change
     */
    protected void notifyAllLemmaDatabaseChangeListeners(LemmaDatabaseUpdateListener.Type type, Formula lemma) {
        for(LemmaDatabaseUpdateListener listener : this.listeners) {
            listener.lemmaDatabaseUpdated(this, type, lemma);
        }
    }

    /**
     * Returns all implications contained in lemma database
     * @return Implications contained in lemma database
     */
    public synchronized Set<Implication> getAllImplications() {
        return new LinkedHashSet<Implication>(this.implications);
    }

    /**
     * Returns all equations contained in lemma database
     * @return Equations contained in lemma database
     */
    public synchronized Set<Equation> getAllEquations() {
        return new LinkedHashSet<Equation>(this.equations);
    }

    public void importTXTDatabase(File file, boolean consistencyCheck) {

        try {
            this.deleteAll();

            // open a buffered stream to read the input file
            FileReader fr = new FileReader(file);
            BufferedReader br = new BufferedReader(fr);

            FormulaParser formulaParser = FormulaParser.createFormulaParser(this.program);
            ArrayList<Formula> newLemmas = formulaParser.parseFormula(br);

            for (Formula formula : newLemmas) {
                this.insert(formula,null);
            }

            this.buildUpIndex(consistencyCheck);

        }catch(FileNotFoundException e) {
            e.printStackTrace();
        }
        catch(IOException e) {
            e.printStackTrace();
        }
        catch(Exception e) {
            e.printStackTrace();
        }

        if(Globals.DEBUG_DICKMEIS){
            System.out.println("DEBUG_DICKMEIS: LDB imported equations" + this.getAllEquations());
        }
    }

    /**
     * Builds a lemma database entry from a formula and a proof
     */
    protected LemmaDatabaseEntry buildLemmaDatabaseEntry(Formula formula) {

        Map<DefFunctionSymbol,Set<Rule>> rules = new LinkedHashMap<DefFunctionSymbol,Set<Rule>>();

        Set<DefFunctionSymbol> allDefFunctionSymbols = formula.getAllDefFunctionSymbols();
        FunctionSymbolGraph fsg = this.program.getCallGraph(false);

        Set<DefFunctionSymbol> defFuntionSymbols = this.getDependendFunctions(
                allDefFunctionSymbols, fsg);

        for(DefFunctionSymbol defFunctionSymbol : defFuntionSymbols) {
            rules.put( defFunctionSymbol, this.program.getAllRules(defFunctionSymbol));
        }

        return new LemmaDatabaseEntry(this.getNextPrimaryKey(), null, formula, rules, this.getDependendSorts(defFuntionSymbols, this.program));
    }

    /**
     * Builds the index from lemma database entries
      * @param consistencyCheck whether only the lemmas which are consistent with the program should be used
     */
    protected void buildUpIndex(boolean consistencyCheck) {

        for(LemmaDatabaseEntry setEntry : this.lemmaDatabaseEntries.values()) {

            boolean insert = !consistencyCheck || (consistencyCheck && (this.program != null));

            if( consistencyCheck && this.program != null ) {

                // get all rules which lemma depends on
                Map<DefFunctionSymbol,Set<Rule>> rules = setEntry.getRules();

                // check if all rules are contained by the current program
                for(Map.Entry<DefFunctionSymbol,Set<Rule>> mapEntry : rules.entrySet() ) {
                    DefFunctionSymbol defFunctionSymbol = mapEntry.getKey();
                    if( !this.program.getRules(defFunctionSymbol).equals(mapEntry.getValue()) ) {
                        insert = false;
                    }
                }

                // check if all typedefinitions which lemma depends on are contained in the
                // current program
                if(!this.getDependendSorts(setEntry.getRules().keySet(),this.program).containsAll(setEntry.getSorts())) {
                    insert = false;
                }

            }

            // if all these checks are passed succesfully add this lemma
            if(insert ) {
                this.insert(setEntry.getFormula(), null, false);
            }
        }
    }

    /**
     * Calculates the functions the given functionsymbols depend on.
     */
    protected Set<DefFunctionSymbol> getDependendFunctions(Set<DefFunctionSymbol> defFunctionSymbols, FunctionSymbolGraph graph) {

        LinkedHashSet<DefFunctionSymbol> result = new LinkedHashSet<DefFunctionSymbol>();

        for(DefFunctionSymbol defFunctionSymbol : defFunctionSymbols) {
            result.addAll(this.getDependendFunctions(defFunctionSymbol, graph));
        }

        return result;
    }

    /**
     * Calculates the functions the given funtionssymbol depends on.
     */
    protected Set<DefFunctionSymbol> getDependendFunctions(DefFunctionSymbol defFunctionSymbol, FunctionSymbolGraph graph) {

        Set<DefFunctionSymbol> result = new LinkedHashSet<DefFunctionSymbol>();

        Set<Node<DefFunctionSymbol>> nodes = new LinkedHashSet<Node<DefFunctionSymbol>>();
        nodes.add(graph.getNodeFromObject(defFunctionSymbol));

        Set<Node<DefFunctionSymbol>> reachableNodes = graph.determineReachableNodes(nodes);

        for(Node<DefFunctionSymbol> node : reachableNodes) {
            result.add(node.getObject());
        }

        return result;
    }

    /**
     * Calculates all type definitions the given functionsymbols depend on.
     */
    protected Set<Sort> getDependendSorts(Set<DefFunctionSymbol> defFunctionSymbols, Program program) {

        Set<Sort> sorts = new LinkedHashSet<Sort>();

        for(DefFunctionSymbol defFunctionSymbol : defFunctionSymbols) {
            sorts.addAll(defFunctionSymbol.getArgSorts());
            sorts.add(defFunctionSymbol.getSort());
        }

        return sorts;
    }

    /**
     * Called when the current programs changes
     * @param consistencyCheck whether only the lemmas which are consistent with the program should be used
     */
    public void programUpdated(Program program, boolean consistencyCheck) {

        this.program = program;
        this.resetIndex();

        if( program != null ) {
            this.buildUpIndex(consistencyCheck);
        }
    }

    /**
     * Reinits the index
     */
    protected void resetIndex() {

        this.root             = new IndexNode(null,null);
        this.formulas       = new LinkedHashSet<Formula>();
        this.implications    = new LinkedHashSet<Implication>();
        this.equations        = new LinkedHashSet<Equation>();

        this.notifyAllLemmaDatabaseChangeListeners(LemmaDatabaseUpdateListener.Type.REMOVE_ALL, null);
    }

    /**
     * Rebuilds the index whereby the options consistency and orientation are respected
      * @param consistencyCheck whether only the lemmas which are consistent with the program should be used
     * @param orientationCheck whether only the lemmas which can be oriented should be used
     */
    public void rebuildIndex(boolean consistencyCheck) {
        this.resetIndex();
        this.buildUpIndex(consistencyCheck);
    }

    /**
     * Returns the number of formulas currently contained in the lemma database
     * @return Number of formulas
     */
    public int getSize() {
        return this.formulas.size();
    }

    /**
     *
     * @param pair
     * @return
     */
    public LemmaDatabaseEntry getLemmaDatabaseEntry(Formula formula) {
        return this.lemmaDatabaseEntries.get(formula);
    }

}


