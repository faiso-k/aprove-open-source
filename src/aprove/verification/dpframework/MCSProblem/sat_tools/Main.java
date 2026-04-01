package aprove.verification.dpframework.MCSProblem.sat_tools;
import java.util.*;


public class Main {

    public static void main(String[] args)
    {
//        ArrayList<List<String>> cnf = new ArrayList<List<String>>();
//        String[][] cnfArrays={{"x"},{"y","-x"},{"-y"}};
//        for (int i=0; i<cnfArrays.length; i++)
//            cnf.add(Arrays.asList(cnfArrays[i]));
//        SatFormula satFormula = new SatFormula(cnf);
//        System.out.println(satFormula);

        String[] clause1 = {"-x","y"};
        String[] clause2 = {"-x","-y"};
        String[] clause3 = {"x"};
        SatFormulaBuilder sfb = new SatFormulaBuilder();
        sfb.addClause(Arrays.asList(clause1));
        sfb.addClause(Arrays.asList(clause2));
        sfb.addClause(Arrays.asList(clause3));
        System.out.println(sfb.satFormula());

//        sfb.unitPropogation();
//        System.out.println(sfb.satFormula());
//        String[] vars = {"x","y","z"};
//        SatFormulaBuilder sfb = new SatFormulaBuilder();
//        String tseitin = sfb.arrowOrOperator("left", vars);
//        sfb.unit(tseitin);
//
//        sfb.unit("left"); sfb.unit("-x"); sfb.unit("-y");
//
//        SatFormula sf = sfb.satFormula();
//        System.out.println(sf);
//        String[] solution = sf.getSolution();
//        for (int i=0; i<solution.length; i++)
//            System.out.print(solution[i]+" ");
//        System.out.println();
    }

}
