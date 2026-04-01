package aprove.verification.dpframework.MCSProblem.sat_tools;
import java.util.*;

/*
 * The current class creates object SatFormula
 * If gets SAT formula e4xpressions and adds it as CNF clauses to SatFormula
 *
 */
public class SatFormulaBuilder {

    public static final int SPLIT_SIZE=100000000;

    List<List<String>> _formula = new ArrayList<List<String>>();
    private int _nextVar = 1;

    private List<List<Integer>> _dimacsCnfFormula = new ArrayList<List<Integer>>();
    int _nextDimacsVar = 1;
    // mutual mapping between string variables form and dimacs one4s
    // used if Config.USE_CNF_FILE=true.
    private Hashtable<Integer,String> _dimacsVarsToVarsHT = new Hashtable<Integer,String>();
    private Hashtable<String,Integer> _varsToDimacsVarsHT = new Hashtable<String,Integer>();

    // the formula we are building
    private SatFormula _satFormula = null;


    public SatFormulaBuilder()
    {
        if (Config.USE_CNF_FILE) {
            this._satFormula = new SatFormula(this._dimacsVarsToVarsHT,this._varsToDimacsVarsHT);
        }
    }

    private void addClausePrivate(String[] clause) {
//        if (clause.length>100)
//            System.out.println(clause.length);

        if (Config.OLD_METHOD) {
            this._formula.add(Arrays.asList(clause));
        } else {
            String literal = null;
            String var = null;
            boolean isNegative = false;
            Integer dimacsVar = null;

            List<Integer> dimacsClosure = new ArrayList<Integer>();
            // _dimacsCnfFormula.add(dimacsClosure);

            for (int i=0; i<clause.length; i++) {
                literal = clause[i];
                var = CommonOperations.literalToVar(literal);
                isNegative = CommonOperations.isLiteralNegative(literal);
                if (!this._varsToDimacsVarsHT.containsKey(var)) { //create new dimacs var
                    this._varsToDimacsVarsHT.put(var,this._nextDimacsVar);
                    this._dimacsVarsToVarsHT.put(this._nextDimacsVar,var);
                    this._nextDimacsVar++;
                }
                dimacsVar = this._varsToDimacsVarsHT.get(var);
                if (isNegative) {
                    dimacsClosure.add(-dimacsVar);
                } else {
                    dimacsClosure.add(dimacsVar);
                }
            }
            if (Config.USE_CNF_FILE) {
                this._satFormula.addClause(dimacsClosure);
            } else {
                this._dimacsCnfFormula.add(dimacsClosure);
            }
        }
    }


    private void addClausePrivate(List<String> clause) {
//        if (clause.size()>100)
//            System.out.println(clause.size());

        if (Config.OLD_METHOD) {
            this._formula.add(clause);
        } else {
            String literal = null;
            String var = null;
            boolean isNegative = false;
            Integer dimacsVar = null;

            List<Integer> dimacsClosure = new ArrayList<Integer>();
            //_dimacsCnfFormula.add(dimacsClosure);

            for (Iterator<String> closureIt = clause.iterator(); closureIt.hasNext(); ) {
                literal = closureIt.next();
                var = CommonOperations.literalToVar(literal);
                isNegative = CommonOperations.isLiteralNegative(literal);
                if (!this._varsToDimacsVarsHT.containsKey(var)) { //create new dimacs var
                    this._varsToDimacsVarsHT.put(var,this._nextDimacsVar);
                    this._dimacsVarsToVarsHT.put(this._nextDimacsVar,var);
                    this._nextDimacsVar++;
                }
                dimacsVar = this._varsToDimacsVarsHT.get(var);
                if (isNegative) {
                    dimacsClosure.add(-dimacsVar);
                } else {
                    dimacsClosure.add(dimacsVar);
                }
            }
            if (Config.USE_CNF_FILE) {
                this._satFormula.addClause(dimacsClosure);
            } else {
                this._dimacsCnfFormula.add(dimacsClosure);
            }
        }
    }


    private String generateNextVar(String prefix)
    {
        String res = prefix+"_"+this._nextVar;
        this._nextVar++;
        return res;
    }

    private String generateNextVar()
    {
        return    this.generateNextVar("VAR");
    }

    public void addClause(List<String> clause)
    {
        this.addClausePrivate(clause);
    }

    // exactly one variable from vars is true
    public void exactlyOne(String[] vars)
    {
        List<List<String>> newPart = new ArrayList<List<String>>();
        for (int i=0; i<vars.length-1; i++) {
            for (int j=i+1; j<vars.length; j++) {
                if (vars[i].equals(vars[j])) {
                    throw new RuntimeException("exactlyOne(): "+vars[i]+" variable appears miore than once.");
                }
                String[] closure = {"-"+vars[i],"-"+vars[j]};
                newPart.add(Arrays.asList(closure));
            }
        }
        newPart.add(Arrays.asList(vars)); //at least one
        for (Iterator<List<String>> it=newPart.iterator(); it.hasNext(); ) {
            this.addClausePrivate(it.next());
        }
    }

    // exactly one variable from vars is true, create tseitin and return it
    public String exactlyOneTseitin(String[] vars)
    {
        String tseitin = this.generateNextVar("TseitinExactlyOne");
        List<List<String>> newPart = new ArrayList<List<String>>();

        // for each i and j
        // 1 <-> vars[i] ^ and[j]
        for (int i=0; i<vars.length-1; i++) {
            for (int j=i+1; j<vars.length; j++) {
                if (vars[i].equals(vars[j])) {
                    throw new RuntimeException("exactlyOner(): "+vars[i]+" variable appears miore than once.");
                }
                String[] closure = {CommonOperations.negateLiteral(tseitin),CommonOperations.negateLiteral(vars[i]),CommonOperations.negateLiteral(vars[j])};
                newPart.add(Arrays.asList(closure));
            }
        }

        // 0 <-> 1 0 ... 0
        // 0 <-> 0 1 ... 0
        // ...
        // 0 <-> 0 ... 0 1
        for (int i=0; i<vars.length-1; i++) {
            String[] closure = new String[vars.length+1];
            closure[0] = tseitin;
            for (int j=0; j<vars.length; j++) {
                closure[j+1] = vars[j];
            }
            closure[i+1] = CommonOperations.negateLiteral(vars[i]);
            newPart.add(Arrays.asList(closure));
        }

        //_formula.addAll(newPart);
        for (Iterator<List<String>> it=newPart.iterator(); it.hasNext(); ) {
            this.addClausePrivate(it.next());
        }

        return tseitin;
    }


    // {var}
    public void unit(String var)
    {
        String[] closure = {var};
        this.addClausePrivate(Arrays.asList(closure));
    }

    //left<->right
    public void iffOperator(String left, String right)
    {
        String[] closure1 = {"-"+left,right};
        String[] closure2 = {left,"-"+right};
        this.addClausePrivate(Arrays.asList(closure1));
        this.addClausePrivate(Arrays.asList(closure2));
    }

    //left->right
    public void arrowOperator(String left, String right)
    {
        String[] closure = {"-"+left,right};
        this.addClausePrivate(Arrays.asList(closure));
    }

    //left->right1 v right2
    public void arrowOrOperator(String left, String right1,String right2)
    {
        String[] closure = {"-"+left,right1,right2};
        this.addClausePrivate(Arrays.asList(closure));
    }

    //left->right1 v right2
    public void arrowAndOperator(String left, String right1, String right2)
    {
        String[] closure1 = {"-"+left,right1};
        String[] closure2 = {"-"+left,right2};
        this.addClausePrivate(Arrays.asList(closure1));
        this.addClausePrivate(Arrays.asList(closure2));
    }

    //tseitin <-> (left <-> right)
    public String iffTseitinOperator(String left, String right)
    {
        // 1 0 1
        // 1 1 0
        // 0 0 0
        // 0 1 1
        String tseitin=this.generateNextVar("TseitinIff");
        String[] closure1 = {CommonOperations.negateLiteral(tseitin),left,CommonOperations.negateLiteral(right)};
        this.addClausePrivate(Arrays.asList(closure1));
        String[] closure2 = {CommonOperations.negateLiteral(tseitin),CommonOperations.negateLiteral(left),right};
        this.addClausePrivate(Arrays.asList(closure2));
        String[] closure3 = {tseitin,left,right};
        this.addClausePrivate(Arrays.asList(closure3));
        String[] closure4 = {tseitin,CommonOperations.negateLiteral(left),CommonOperations.negateLiteral(right)};
        this.addClausePrivate(Arrays.asList(closure4));

        return tseitin;
    }

    //leftmost <-> (left ^ right)
    public void andOperator(String leftmost, String left, String right)
    {
        // 1 0 _
        String[] closure1 = {CommonOperations.negateLiteral(leftmost),left};
        this.addClausePrivate(closure1);

        // 1 _ 0
        String[] closure2 = {CommonOperations.negateLiteral(leftmost),right};
        this.addClausePrivate(closure2);

        // 0 1 1
        String[] closure3 = {leftmost,CommonOperations.negateLiteral(left),CommonOperations.negateLiteral(right)};
        this.addClausePrivate(closure3);
    }

    //tseitin <-> (left ^ right)
    public String andOperatorTseitin(String left, String right)
    {
        String tseitin=this.generateNextVar("TseitinAnd");
        this.andOperator(tseitin,left,right);
        return tseitin;
    }

    //Tseitin <-> left -> (right[0] v right[1] v ... v right[n-1])
    //returns Tseitin
    public String arrowOrOperator(String left, String[] right)
    {
        String tseitin=this.generateNextVar("TseitinArrowOr");

        // 1 1 0 0 ... 0
        String[] closure = new String[right.length+2];
        closure[0] = CommonOperations.negateLiteral(tseitin);
        closure[1] = CommonOperations.negateLiteral(left);
        for (int i=0; i<right.length; i++) {
            closure[i+2] = right[i];
        }
        this.addClausePrivate(closure);

        // 0 0
        String[] closure2 = {tseitin,left};
        this.addClausePrivate(closure2);

        // 0 1 1
        // 0 1 _ 1
        // 0 1 _ _ 1
        // ...
        // 0 1 _ _ _ ... _ 1
        for (int i=0; i<right.length; i++) {
            closure = new String[3];
            closure[0] = tseitin;
            closure[1] = CommonOperations.negateLiteral(left);
            closure[2] = CommonOperations.negateLiteral(right[i]);
            this.addClausePrivate(closure);
        }
        return tseitin;
    }


    //left -> (right[0] ^ right[1] ^ ... ^ right[n-1])
    public void arrowAndOperator(String left, String[] right)
    {
        // 1 0 _ ... _
        // 1 _ 0 ... _
        // ...
        // 1 _ _ ... 0
        for (int i=0; i<right.length; i++) {
            String[] closure = new String[2];
            closure[0] = CommonOperations.negateLiteral(left);
            closure[1] = right[i];
            this.addClausePrivate(closure);
        }
    }

    //left <-> (right[0] ^ right[1] ^ ... ^ right[n-1])
    public void iffAndOperatorDirect(String left, String[] right)
    {
        // 0 1 1 ... 1
        String[] closure = new String[right.length+1];
        closure[0] = left;
        for (int i=0; i<right.length; i++) {
            closure[i+1] = CommonOperations.negateLiteral(right[i]);
        }
        this.addClausePrivate(closure);

        // 1 0
        // 1 _ 0
        // 1 _ _ 0
        // ...
        // 1 _ _ _ ... _ 0
        for (int i=0; i<right.length; i++) {
            closure = new String[2];
            closure[0] = CommonOperations.negateLiteral(left);
            closure[1] = right[i];
            this.addClausePrivate(closure);
        }
    }

    //tseitin <-> (right[0] ^ right[1] ^ ... ^ right[n-1])
    public String iffAndOperatorDirectTseitin(String[] vars)
    {
        String tseitin = this.generateNextVar("TseitinAnd");
        this.iffAndOperator(tseitin,vars);
        return tseitin;
    }

    public void iffAndOperator(String left,String[] vars)
    {
        if (vars.length<=SatFormulaBuilder.SPLIT_SIZE) {
            this.iffAndOperatorDirect(left,vars);
            return;
        }
        String[] first = new String[vars.length/2];
        String[] second = new String[vars.length-vars.length/2];
        for (int i=0; i<first.length; i++) {
            first[i]=vars[i];
        }
        for (int i=0; i<second.length; i++) {
            second[i]=vars[first.length+i];
        }
        String firstTs = this.iffAndOperatorTseitin(first);
        String secondTs = this.iffAndOperatorTseitin(second);

        this.iffAndOperatorDirect(left,new String[] {firstTs,secondTs});

    }

    public String iffAndOperatorTseitin(String[] vars)
    {
        String tseitin=this.generateNextVar("TseitinAnd");
        this.iffAndOperator(tseitin,vars);
        return tseitin;
    }


    //left <-> (vars[0] v vars[1] v ... v vars[n-1])
    public void iffOrOperatorDirect(String left,String[] vars)
    {
        //String tseitin=generateNextVar("TseitinOr");

        // 1 0 0 ... 0
        String[] closure = new String[vars.length+1];
        closure[0] = CommonOperations.negateLiteral(left);
        for (int i=0; i<vars.length; i++) {
            closure[i+1] = vars[i];
        }
        this.addClausePrivate(closure);

        // 0 1
        // 0 _ 1
        // 0 _ _ 1
        // ...
        // 0 _ _ _ ... _ 1
        for (int i=0; i<vars.length; i++) {
            closure = new String[2];
            closure[0] = left;
            closure[1] = CommonOperations.negateLiteral(vars[i]);
            this.addClausePrivate(closure);
        }
    }

    public String iffOrOperatorDirectTseitin(String[] vars)
    {
        String tseitin=this.generateNextVar("TseitinOr");
        this.iffOrOperatorDirect(tseitin,vars);
        return tseitin;
    }

    public void iffOrOperator(String left,String[] vars)
    {
        if (vars.length<=SatFormulaBuilder.SPLIT_SIZE) {
            this.iffOrOperatorDirect(left,vars);
            return;
        }
        String[] first = new String[vars.length/2];
        String[] second = new String[vars.length-vars.length/2];
        for (int i=0; i<first.length; i++) {
            first[i]=vars[i];
        }
        for (int i=0; i<second.length; i++) {
            second[i]=vars[first.length+i];
        }
        String firstTs = this.iffOrOperatorTseitin(first);
        String secondTs = this.iffOrOperatorTseitin(second);

        this.iffOrOperatorDirect(left,new String[] {firstTs,secondTs});

    }

    public String iffOrOperatorTseitin(String[] vars)
    {
        String tseitin=this.generateNextVar("TseitinOr");
        this.iffOrOperator(tseitin,vars);
        return tseitin;
    }

    public void unary(String[] vars)
    {
        for (int i=0; i<vars.length-1; i++) {
            String[] closure = new String[2];
            closure[0] = vars[i];
            closure[1] = CommonOperations.negateLiteral(vars[i+1]);
            this.addClausePrivate(closure);
        }
    }

    // left <=> right1 != right2
    public void iffUnaryNEQ(String left, String[] right1, String[] right2)
    {
        String right1GTright2 = this.generateNextVar();
        String right2GTright1 = this.generateNextVar();
        this.iffUnaryGT(right1GTright2,right1,right2);
        this.iffUnaryGT(right2GTright1,right2,right1);
        String[] iffOrParams = {right1GTright2,right2GTright1};
        this.iffOrOperator(left,iffOrParams);
    }

    public String iffUnaryNEQTseitin(String[] right1, String[] right2)
    {
        String tseitin=this.generateNextVar("TseitinUnaryNEQ");
        this.iffUnaryNEQ(tseitin,right1,right2);
        return tseitin;
    }

    // left <=> right1 >= right2
    public void iffUnaryGEQ(String left, String[] right1, String[] right2)
    {
        // 0 (0,0) _ ...                 _
        // 0 (1,_) (_,0)   _    _  ...  _
        // 0   _   (1,_) (_,0)  _  ...  _
        //...
        // 0  _    ...          (1,_) (0,_)
        // 0  _    ...                (1,_)
        for (int i=0; i<right1.length-1; i++) {
            String[] clause = new String[3];
            clause[0] = left;
            clause[1] = CommonOperations.negateLiteral(right1[i]);
            clause[2] = right2[i+1];
            this.addClausePrivate(clause);
        }
        String[] clause2 = new String[3];
        clause2[0] = left;
        clause2[1] = right1[0];
        clause2[2] = right2[0];
        this.addClausePrivate(clause2);

        String[] clause3 = new String[2];
        clause3[0] = left;
        clause3[1] = CommonOperations.negateLiteral(right1[right1.length-1]);
        this.addClausePrivate(clause3);

        // 1 (0,1)  _    _  ...  _
        // 1  _   (0,1)  _  ...  _
        //...
        // 1  _    ...         (0,1)
        for (int i=0; i<right1.length; i++) {
            String[] clause = new String[3];
            clause[0] = CommonOperations.negateLiteral(left);
            clause[1] = right1[i];
            clause[2] = CommonOperations.negateLiteral(right2[i]);
            this.addClausePrivate(clause);
        }

    }

    // left <=> right1 >= right2
    public void iffUnaryGT(String left, String[] right1, String[] right2)
    {
        // 1 (0,_)   _          _  ...  _
        // 1 (_,1) (0,_)   _    _  ...  _
        // 1   _   (_,1) (0,_)  _  ...  _
        //...
        // 1  _    ...          (_,1) (0,_)
        // 1  _    ...                (_,1)
        for (int i=0; i<right1.length-1; i++) {
            String[] clause = new String[3];
            clause[0] = CommonOperations.negateLiteral(left);
            clause[1] = right1[i+1];
            clause[2] = CommonOperations.negateLiteral(right2[i]);
            this.addClausePrivate(clause);
        }
        String[] clause2 = new String[2];
        clause2[0] = CommonOperations.negateLiteral(left);
        clause2[1] = right1[0];
        this.addClausePrivate(clause2);

        String[] clause3 = new String[2];
        clause3[0] = CommonOperations.negateLiteral(left);
        clause3[1] = CommonOperations.negateLiteral(right2[right2.length-1]);
        this.addClausePrivate(clause3);

        // 0 (1,0)  _    _  ...  _
        // 0  _   (1,0)  _  ...  _
        //...
        // 0  _    ...         (1,0)
        for (int i=0; i<right1.length; i++) {
            String[] clause = new String[3];
            clause[0] = left;
            clause[1] = CommonOperations.negateLiteral(right1[i]);
            clause[2] = right2[i];
            this.addClausePrivate(clause);
        }

    }

    public String iffUnaryGTTseitin(String[] right1, String[] right2)
    {
        String tseitin=this.generateNextVar("TseitinUnaryGT");
        this.iffUnaryGT(tseitin,right1,right2);
        return tseitin;
    }

    // left <=> right1 >= right2
    public void iffBinaryGEQ(String left, String[] right1, String[] right2)
    {
        // geq(x1..xn,y1..yn) <-> (x1 ^ -y1) v (x1=y1 ^ geq(x2..xn,y2..yn))
        // geq(x2..xn,y2..yn) <-> (x2 ^ -y2) v (x2=y2 ^ geq(x3..xn,y3..yn))
        // ...
        // geq(xn,yn) <-> (xn v -yn)

        // geq1 x y geq2
        // 1    0 1 _
        // 1    0 0 0
        // 1    1 1 0
        // 0    1 0 _
        // 0     _ _ 1
        String current = left;
        for (int i=0; i<right1.length-1; i++) {
            String next=this.generateNextVar("BinaryGEQ");

            String[] closure = new String[3];
            closure[0] = CommonOperations.negateLiteral(current);
            closure[1] = right1[i];
            closure[2] = CommonOperations.negateLiteral(right2[i]);
            this.addClausePrivate(closure);

            closure = new String[4];
            closure[0] = CommonOperations.negateLiteral(current);
            closure[1] = right1[i];
            closure[2] = right2[i];
            closure[3] = next;
            this.addClausePrivate(closure);

            closure = new String[4];
            closure[0] = CommonOperations.negateLiteral(current);
            closure[1] = CommonOperations.negateLiteral(right1[i]);
            closure[2] = CommonOperations.negateLiteral(right2[i]);
            closure[3] = next;
            this.addClausePrivate(closure);

            closure = new String[3];
            closure[0] = current;
            closure[1] = CommonOperations.negateLiteral(right1[i]);
            closure[2] = right2[i];
            this.addClausePrivate(closure);

            closure = new String[2];
            closure[0] = current;
            closure[1] = CommonOperations.negateLiteral(next);
            this.addClausePrivate(closure);

            current = next;
        }
        int i = right1.length-1;

        // geq(xn,yn) <-> (xn v -yn)
        // 1 0 1
        // 0 1 _
        // 0 _ 0
        String[] closure = new String[3];
        closure[0] = CommonOperations.negateLiteral(current);
        closure[1] = right1[i];
        closure[2] = CommonOperations.negateLiteral(right2[i]);
        this.addClausePrivate(closure);

        closure = new String[2];
        closure[0] = current;
        closure[1] = CommonOperations.negateLiteral(right1[i]);
        this.addClausePrivate(closure);

        closure = new String[2];
        closure[0] = current;
        closure[1] = right2[i];
        this.addClausePrivate(closure);
    }

    // left <=> right1 > right2
    public void iffBinaryGT(String left, String[] right1, String[] right2)
    {
        // gt(x1..xn,y1..yn) <-> (x1 ^ -y1) v (x1=y1 ^ gt(x2..xn,y2..yn))
        // gt(x2..xn,y2..yn) <-> (x2 ^ -y2) v (x2=y2 ^ gt(x3..xn,y3..yn))
        // ...
        // gt(xn,yn) <-> (xn ^ -yn)

        // geq1 x y geq2
        // 1    0 1 _
        // 1    0 0 0
        // 1    1 1 0
        // 0    1 0 _
        // 0     _ _ 1
        String current = left;
        for (int i=0; i<right1.length-1; i++) {
            String next=this.generateNextVar("BinaryGT");

            String[] closure = new String[3];
            closure[0] = CommonOperations.negateLiteral(current);
            closure[1] = right1[i];
            closure[2] = CommonOperations.negateLiteral(right2[i]);
            this.addClausePrivate(closure);

            closure = new String[4];
            closure[0] = CommonOperations.negateLiteral(current);
            closure[1] = right1[i];
            closure[2] = right2[i];
            closure[3] = next;
            this.addClausePrivate(closure);

            closure = new String[4];
            closure[0] = CommonOperations.negateLiteral(current);
            closure[1] = CommonOperations.negateLiteral(right1[i]);
            closure[2] = CommonOperations.negateLiteral(right2[i]);
            closure[3] = next;
            this.addClausePrivate(closure);

            closure = new String[3];
            closure[0] = current;
            closure[1] = CommonOperations.negateLiteral(right1[i]);
            closure[2] = right2[i];
            this.addClausePrivate(closure);

            closure = new String[2];
            closure[0] = current;
            closure[1] = CommonOperations.negateLiteral(next);
            this.addClausePrivate(closure);

            current = next;
        }
        int i = right1.length-1;

        // get(xn,yn) <-> (xn ^ -yn)
        // 1 0 _
        // 1 _ 1
        // 0 0 1
        String[] closure = new String[2];
        closure[0] = CommonOperations.negateLiteral(current);
        closure[1] = right1[i];
        this.addClausePrivate(closure);

        closure = new String[2];
        closure[0] = CommonOperations.negateLiteral(current);
        closure[1] = CommonOperations.negateLiteral(right2[i]);
        this.addClausePrivate(closure);

        closure = new String[3];
        closure[0] = current;
        closure[1] = right1[i];
        closure[2] = CommonOperations.negateLiteral(right2[i]);
        this.addClausePrivate(closure);
    }

    public String iffBinaryGTTseitin(String[] right1, String[] right2)
    {
        String tseitin=this.generateNextVar("TseitinBinaryGT");
        this.iffBinaryGT(tseitin,right1,right2);
        return tseitin;
    }

    // left <=> right1 != right2
    public void iffBinaryNEQ(String left, String[] right1, String[] right2)
    {
        String right1GTright2 = this.generateNextVar();
        String right2GTright1 = this.generateNextVar();
        this.iffBinaryGT(right1GTright2,right1,right2);
        this.iffBinaryGT(right2GTright1,right2,right1);
        String[] iffOrParams = {right1GTright2,right2GTright1};
        this.iffOrOperator(left,iffOrParams);
    }

    public String iffBinaryNEQTseitin(String[] right1, String[] right2)
    {
        String tseitin=this.generateNextVar("TseitinBinaryNEQ");
        this.iffBinaryNEQ(tseitin,right1,right2);
        return tseitin;
    }

    // return SAT formula
    public SatFormula satFormula()
    {
        if (Config.OLD_METHOD) {
            return new SatFormula(this._formula);
        } else {
            if (Config.USE_CNF_FILE) {
                return this._satFormula;
            } else {
                return new SatFormula(this._dimacsCnfFormula,this._dimacsVarsToVarsHT,this._varsToDimacsVarsHT);
            }
        }
    }
}
