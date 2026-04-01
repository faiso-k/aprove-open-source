package aprove.verification.dpframework.MCSProblem.mcnp;

import java.util.*;
import java.util.Map.Entry;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.MCSProblem.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class MCGraph {

    private final static String ARGS_RELATION_SEPARATOR = "ARGS_RELATION_SEPARATOR";

    private final static String EQ = "=";
    private final static String GE = ">=";
    private final static String GT = ">";

    private static int idNum = 0;

    private String ID;
    private ProgramPoint _point1; //source program point
    private ProgramPoint _point2; //target program point

    //key: x_seperator_y, value: > or >=
    private Hashtable<String,String> _argsRelationsHT = new Hashtable<String,String>();

    // Throws exception if relation type is invalid: not < <= = > >=
    private void validateRelationType(String relationType)
    {
        if (!relationType.equals(MCGraph.GT) && !relationType.equals(MCGraph.GE) && !relationType.equals(MCGraph.EQ)) {
            Logger.writeError("Wrong atguments relation type: "+relationType+".");
            throw new RuntimeException("Wrong atguments relation type: "+relationType+".");
        }
    }

    // Return arguments of both program points set
    private Set<Argument> gatAllArgumentsSet()
    {
        Set<Argument> argumentsSet = new HashSet<Argument>(this._point1.getArgumentsSet());
        argumentsSet.addAll(this._point2.getArgumentsSet());
        return argumentsSet;
    }

    public MCGraph(ProgramPoint point1,    ProgramPoint point2, String[][] relations)
    {
        this._point1=point1;
        this._point2=point2;

        this.ID="G-"+this._point1.getID()+"-"+this._point2.getID()+"-"+MCGraph.idNum;
        MCGraph.idNum++;

        Set<Argument> argsSet = this.gatAllArgumentsSet();

        for (int i=0; i<relations.length; i++)    {
            Argument arg1 = new Argument(relations[i][0]);
            Argument arg2 = new Argument(relations[i][1]);
            String relationType = relations[i][2];

            this.validateRelationType(relationType);

            if (!argsSet.contains(arg1) || !argsSet.contains(arg2)) {
                String errorMsg = "Arguments "+arg1+" or "+arg2+" does not appear in program points "+this._point1+" and "+this._point2;
                Logger.writeError(errorMsg);
                throw new RuntimeException(errorMsg);
            }
            else {
                if (relationType.equals("=")) { //input x=y is transtated to x>=y an d y>=x
                    this._argsRelationsHT.put(arg1+MCGraph.ARGS_RELATION_SEPARATOR+arg2, MCGraph.GE);
                    this._argsRelationsHT.put(arg2+MCGraph.ARGS_RELATION_SEPARATOR+arg1, MCGraph.GE);
                } else {
                    this._argsRelationsHT.put(arg1+MCGraph.ARGS_RELATION_SEPARATOR+arg2, relationType);
                }
            }
        }
    }

    public String getID()
    {
        return this.ID;
    }

    public ProgramPoint getPointFrom()
    {
        return this._point1;
    }

    public ProgramPoint getPointTo()
    {
        return this._point2;
    }

    // Returns relation R such that (arg1 R arg2)
    // If no such return null
    public String getRelation(Argument arg1, Argument arg2)
    {
        String key = arg1 + MCGraph.ARGS_RELATION_SEPARATOR + arg2;
        if (!this._argsRelationsHT.containsKey(key)) {
            return null;
        } else {
            return this._argsRelationsHT.get(key);
        }
    }

    // adds relations. If x>y, y>=z adds x>z
    public void transitiveClosure()
    {
        Set<Argument> args = this.gatAllArgumentsSet();

        boolean updated = true;
        while (updated) {
            updated = false;
            for (Iterator<Argument> itFrom=args.iterator(); itFrom.hasNext(); ) {
                Argument from = itFrom.next();
                for (Iterator<Argument> itTo=args.iterator(); itTo.hasNext(); ) {
                    Argument to = itTo.next();
                    String initialRelation = this.getRelation(from,to);
                    if (!from.equals(to) && (initialRelation==null || initialRelation.equals(MCGraph.GE))) { //if there is strict edge, nothing to update
                        for (Iterator<Argument> itMiddle=args.iterator(); itMiddle.hasNext(); ) {
                            Argument middle = itMiddle.next();
                            String firstPart = this.getRelation(from,middle);
                            String secondPart = this.getRelation(middle,to);
                            if (firstPart!=null && secondPart!=null) {
                                //new edge is strict
                                if (firstPart.equals(">") || secondPart.equals(">")) {
                                    this._argsRelationsHT.put(from+MCGraph.ARGS_RELATION_SEPARATOR+to, MCGraph.GT);
                                    updated = true;
                                } else if (initialRelation==null) {
                                    this._argsRelationsHT.put(from+MCGraph.ARGS_RELATION_SEPARATOR+to, MCGraph.GE);
                                    updated = true;
                                }
                            }
                        }
                    } //if no strict edge from->to
                }
            }
        } //while
    }

    public int getNumOfEdges() {
        return this._argsRelationsHT.keySet().size();
    }

    public int getNumOfNodes() {
        return this._point1.getArguments().length+this._point2.getArguments().length;
    }

    public int getNumOfVerticses() {
        return this._point1.getArguments().length + this._point2.getArguments().length;
    }

    public int getNumOfNodesPerProgramPoint() {
        return Math.max(this._point1.getArguments().length,this._point2.getArguments().length);
    }

    @Override
    public String toString()
    {
        String arrows="{";
        for (Iterator<String> it=this._argsRelationsHT.keySet().iterator(); it.hasNext() ;) {
            String argsKey = it.next();
            String relationType =  this._argsRelationsHT.get(argsKey);
            String[] args = argsKey.split(MCGraph.ARGS_RELATION_SEPARATOR);
            arrows=arrows+"("+args[0]+""+relationType+""+args[1]+")"+",";
        }
        arrows=arrows.substring(0,arrows.length()-1)+"}";
        return "["+this._point1+" "+this._point2+" "+arrows+"]";
    }

    public MCRule toMCRule() {
        TRSFunctionApplication left = this._point1.toFunctionApplication();
        TRSFunctionApplication right = this._point2.toFunctionApplication();
        MCOrderConstraints orderConstraints = this.relationsToMCOrderConstraints();
        MCRule res = MCRule.create(left, right, orderConstraints);
        return res;
    }

    public MCOrderConstraints relationsToMCOrderConstraints() {
        Map<MCVarPair, MCRelation> varsToRel = new LinkedHashMap<MCVarPair, MCRelation>();
        for (Entry<String, String> twoVarsToRel : this._argsRelationsHT.entrySet()) {
            String twoVars = twoVarsToRel.getKey();

            // TODO get that separator out of the code to ensure correctness ...
            String[] vars = twoVars.split(MCGraph.ARGS_RELATION_SEPARATOR);
            assert vars.length == 2;
            TRSVariable v1 = TRSTerm.createVariable(vars[0]);
            TRSVariable v2 = TRSTerm.createVariable(vars[1]);
            String rel = twoVarsToRel.getValue();
            MCRelation mcRel = MCRelation.fromRepresentation(rel);
             Pair<MCVarPair, MCRelation> varPairRel = MCVarPair.toEntry(v1, v2, mcRel);
             varsToRel.put(varPairRel.x, varPairRel.y);
        }
        ImmutableMap<MCVarPair, MCRelation> immutableVarsToRel = ImmutableCreator.create(varsToRel);
        MCOrderConstraints res = MCOrderConstraints.createFromMCVarPairMap(immutableVarsToRel);
        return res;
    }

    public static MCGraph createFromMCRule(MCRule mcRule) {

        // convert the program points ...
        TRSFunctionApplication left = mcRule.getLeft();
        TRSFunctionApplication right = mcRule.getRight();
        ProgramPoint p1 = MCGraph.functionApplicationToProgramPoint(left);
        ProgramPoint p2 = MCGraph.functionApplicationToProgramPoint(right);

        // ... and also convert the constraints
        MCOrderConstraints constraints = mcRule.getConstraints();
        Map<MCVarPair, MCRelation> varPairToRelation = constraints.getConstraints();
        int length = varPairToRelation.size();
        String[][] relations = new String[length][3];
        int i = 0;
        for (Entry<MCVarPair, MCRelation> vpToRel : varPairToRelation.entrySet()) {
            MCVarPair vp = vpToRel.getKey();
            MCRelation rel = vpToRel.getValue();
            switch (rel) {
            case LT : // reverse
                relations[i][0] = vp.getSecond().toString();
                relations[i][1] = vp.getFirst().toString();
                relations[i][2] = MCGraph.GT;
                break;
            case LE : // reverse
                relations[i][0] = vp.getSecond().toString();
                relations[i][1] = vp.getFirst().toString();
                relations[i][2] = MCGraph.GE;
                break;
            case EQ :
                relations[i][0] = vp.getFirst().toString();
                relations[i][1] = vp.getSecond().toString();
                relations[i][2] = MCGraph.EQ;
                break;
            case GE :
                relations[i][0] = vp.getFirst().toString();
                relations[i][1] = vp.getSecond().toString();
                relations[i][2] = MCGraph.GE;
                break;
            case GT :
                relations[i][0] = vp.getFirst().toString();
                relations[i][1] = vp.getSecond().toString();
                relations[i][2] = MCGraph.GT;
                break;
            default :
                throw new RuntimeException("Unknown relation " + rel + '!');
            }
            ++i;
        }

        // build graph
        MCGraph res = new MCGraph(p1, p2, relations);
        return res;
    }

    private static ProgramPoint functionApplicationToProgramPoint(TRSFunctionApplication fApp) {
        List<TRSTerm> oldArgs = fApp.getArguments();
        int length = oldArgs.size();
        if (Globals.useAssertions) {
            for (TRSTerm arg : oldArgs) {
                assert arg.isVariable();
            }
        }
        // note that Igor's code can also distinguish program points
        // of different arities
        String newName = fApp.getRootSymbol().getName();
        String[] newArgs = new String[length];
        for (int i = 0; i < length; ++i) {
            newArgs[i] = oldArgs.get(i).toString();
        }
        ProgramPoint res = new ProgramPoint(newName, newArgs);
        return res;
    }
}

