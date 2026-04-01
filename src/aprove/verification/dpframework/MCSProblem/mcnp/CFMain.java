package aprove.verification.dpframework.MCSProblem.mcnp;

import java.io.*;
import java.util.*;

public class CFMain {

    public static void testFolder(final String dir, final boolean verify) {
        final File dirFile = new File(dir);
        if (!dirFile.exists() || !dirFile.isDirectory()) {
            throw new RuntimeException("Directory " + dir + " does not esist.");
        }

        int succeded = 0;
        int failed = 0;

        int totalTime = 0;

        final File[] files = dirFile.listFiles();
        for (final File file : files) {
            final String fileName = file.getName();
            System.out.println("Proccessing " + fileName + ":");
            try {
                final long startTime = System.currentTimeMillis();
                final Program pr = Program.create(file.getAbsolutePath());
                pr.findLevelMappings();
                final List<MCGraphMapping> rankingFunction = pr.getMcGraphsMappings();
                final long time = System.currentTimeMillis() - startTime;
                totalTime += time;
                final String timeReport = "[" + time / 60000 + ":" + (time / 1000) % 60 + " (" + time + " milisec)]";
                if (rankingFunction != null) {
                    System.out.println("\tOK> " + fileName + " terminates " + timeReport);
                    if (verify && rankingFunction != null) {
                        final Verifier ver = new Verifier();
                        ver.verify(pr.getInitialMCGraphs(), rankingFunction);
                    }
                    succeded++;
                } else {
                    System.out.println("\tERROR> " + fileName + " termination proof failed " + timeReport);
                    failed++;
                }
            } catch (final Exception e) {
                System.err.println("Exception accured!");
                e.printStackTrace();
            }
        }

        System.out.println("Succeeded: " + succeded);
        System.out.println("Failed: " + failed);
        System.out.println("Total: " + files.length);
        final String totalTimeReport =
            "[" + totalTime / (60 * 60 * 1000) + ":" + (totalTime / (60 * 1000)) % 60 + ":" + (totalTime / 1000) % 60
                + " (" + totalTime + " milisec)]";
        System.out.println("Time: " + totalTimeReport);
    }

    public static void main(final String[] args) {

        //        System.out.println(CommonOperations.logUpper(4));
        //        System.out.println(CommonOperations.logUpper(5));

        /*
        String[] xs={"x1","x2","x3"};
        String[] ys={"y1","y2","y3"};
        SatFormulaBuilder sfb = new SatFormulaBuilder();
        sfb.unary(xs);
        sfb.unary(ys);

        sfb.iffBinaryGEQ("unaryTseitin", xs, ys);
        sfb.unit("unaryTseitin");
        sfb.unit("-x3");
        sfb.unit("y2");

        SatFormula f = sfb.satFormula();
        f.getSolution();
        //System.out.println(f);
        for (int i=0; i<xs.length; i++)
            System.out.print(f.getVarValue("x"+(i+1)));
        System.out.println();
        for (int i=0; i<ys.length; i++)
            System.out.print(f.getVarValue("y"+(i+1)));

        if (1==1) return;
        */

        /* iffAnd test
        SatFormulaBuilder sfb = new SatFormulaBuilder();
        String[] right={"x","y","z"};
        sfb.iffAndOperator("left",right);
        sfb.unit("left");
        SatFormula f = sfb.satFormula();
        System.out.println(f);
        System.out.println(Arrays.toString(f.getPositiveSolution()));
        */

        /*
        String graph="f(x1, x2, x3) :- [x1>=y1, x3>y2, x2>=y3] ; g(y1, y2, y3) .";
        String[] graphSplitted = graph.split("(:-)|(;)");
        for (int i=0; i<graphSplitted.length; i++)
            System.out.println(graphSplitted[i].trim());


        String progPointFrom = "f(x1, x2, x3)";
        String[] progPointFromSplitted = progPointFrom.split("\\(|\\)");
        System.out.println(progPointFromSplitted.length);
        for (int i=0; i<progPointFromSplitted.length; i++)
            System.out.println(progPointFromSplitted[i].trim());
         */

        // String dir = "O:\\teza\\Examples\\Ahen\\";

        // args[0] = dir+"CAV02_practical1.txt";         //PROVED
        // args[0] = dir+"CAV02_practical2.txt"; //
        // args[0] = dir+"CAV02_practical3.txt"; //

        //args[0] = dir + "CAV05_c.05.txt"; //contradictive constraints

        // args[0] = dir+"classic_collatz.txt"; //'boolean' '-> x'
        // args[0] = dir+"classic_f91.txt"; //nested
        // args[0] = dir+"classic_maxsort.txt"; //nested

        // args[0] = dir+"csharp_csharp1.txt"; //booleans
        // args[0] = dir+"csharp_csharp2.txt"; //booleans
        // args[0] = dir+"csharp_csharp3.txt"; //booleans

        // args[0] = dir+"ESOP08_abstractions.txt";         //PROVED

        // args[0] = dir+"LICS04_c.01.txt";                 //PROVED
        // args[0] = dir+"LICS04_choice.txt";                //CAN NOT PROVE TERMINATION

        // args[0] = dir+"new_conv.txt";             // '->0', nested
        // args[0] = dir+"new_countdown.txt";         // booleans cd(TRUE, x) -> cd (x > 0, x - 1) to easy
        // args[0] = dir+"new_countUpExp.txt";         // 'nested', '->1'
        // args[0] = dir+"new_countup.txt";                 // boolean PROOVED (easy)
        // args[0] = dir+"new_countUpNo.txt";         // -> 2*x
        // args[0] = dir+"new_divMinus.txt";         // -> div() + 1
        // args[0] = dir+"new_indirect.txt";                 //boolen PROOVED
        // args[0] = dir+"new_powFast.txt";         //boolean, to much arithmetics
        // args[0] = dir+"new_pow.txt";                     // boolean => PROOVED (easy)
        // args[0] = dir+"new_randomFullUpDown.txt"; // nested
        // args[0] = dir+"new_sqrt.txt"; // boolean can not translate
        // args[0] = dir+"new_unsatCond1.txt"; // x>x
        // args[0] = dir+"new_unsatCond2.txt"; // x*x<0

        // args[0] = dir+"paper_ackTen.txt"; // boolean could not translate
        // args[0] = dir+"paper_extra1.txt";         // boolean PROVEN (easy)
        // args[0] = dir+"paper_extra2.txt";         // boolean PROVEN (easy)
        // args[0] = dir+"paper_inclist.txt"; // nested
        // args[0] = dir+"paper_log.txt"; // too complicated expressions
        // args[0] = dir+"paper_sum.txt";             //bool;ean PROVED
        // args[0] = dir+"paper_thousand.txt"; //    almost the same as new_countup

        // args[0] = dir+"parts_div.txt";             //dir+1 changed to div PROVED
        // args[0] = dir+"parts_eratosthenes.txt";     //nested
        // args[0] = dir+"parts_eratosthenes_small.txt";     //nested
        /*
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\AProVEMath.jar_1.mc";

        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\Collatz.jar_1.mc";
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\Convert.jar_1.mc";
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\CountUpRound.jar_1.mc"; //+
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\CountUpRound.jar_2.mc"; //+

        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\DivMinus.jar_1.mc"; //+
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\DivMinus2.jar_1.mc";
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\DivWithoutMinus.jar_1.mc";
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\Duplicate.jar_1.mc";
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\DuplicateNodes.jar_1.mc";

        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\ListContent.jar_1.mc"; // realy can  not terminate
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\ListContentArbitrary.jar_1.mc"; //+
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\ListContentArbitrary.jar_2.mc"; //+ BIG
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\ListContentArbitrary.jar_3.mc";
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\ListContentTail.jar_1.mc"; //+ BIG
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\ListContentTail.jar_2.mc";
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\ListDuplicate.jar_1.mc"; //+
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\Log.jar_1.mc";
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\LogAG.jar_1.mc";
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\LogBuiltin.jar_1.mc";
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\LogIterative.jar_1.mc";
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\LogMult.jar_1.mc";

        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\McCarthyIterative.jar_1.mc";
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\MinusBuiltin.jar_1.mc"; //+
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\MinusMin.jar_1.mc"; //+ mcg 5 an d 7 deleted
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\MinusUserDefined.jar_1.mc";
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\Mod.jar_1.mc";
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\Mod.jar_2.mc";

        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\Overflow.jar_1.mc"; //+
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\Overflow.jar_2.mc"; //+

        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaA1.jar_1.mc"; //+
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaA4.jar_1.mc"; //+
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaA4.jar_2.mc"; //+
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaA5.jar_1.mc"; //+
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaA5.jar_2.mc"; //+
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaA6.jar_1.mc";
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaA7.jar_1.mc"; //+
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaA8.jar_1.mc";
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaA8.jar_2.mc";
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaA9.jar_1.mc"; //+
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaA9.jar_2.mc"; //+
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaA10.jar_1.mc"; //+
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaA10.jar_2.mc"; //+

        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaB1.jar_1.mc"; //+
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaB1.jar_2.mc"; //+
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaB2.jar_1.mc"; //+
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaB3.jar_1.mc"; //+
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaB3.jar_2.mc"; //+
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaB4.jar_1.mc"; //+
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaB4.jar_2.mc"; //+
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaB5.jar_1.mc"; //+
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaB5.jar_2.mc"; //+
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaB6.jar_1.mc"; //+
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaB6.jar_2.mc"; //+
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaB7.jar_1.mc"; //+
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaB8.jar_1.mc";
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaB8.jar_2.mc";
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaB10.jar_1.mc"; //+ unsatisfiable mcg 9 remioved manually
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaB10.jar_2.mc"; //+ unsatisfiable mcg 9 remioved manually
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaB11.jar_1.mc"; //+ BIG unsatisfiable mcg 7 remioved manually
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaB11.jar_2.mc"; //+ BIG (3 Level Mappings)) unsatisfiable mcg 7 remioved manually
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaB12.jar_1.mc"; //+
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaB12.jar_2.mc"; //+
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaB13.jar_1.mc"; //+ BIG mcg 10 and 20 removed manually
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaB13.jar_2.mc"; //+ BIG 4 Level Mappings
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaB14.jar_1.mc";
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaB14.jar_2.mc";
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaB15.jar_1.mc"; //+
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaB15.jar_2.mc"; //+
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaB16.jar_1.mc"; //+
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaB16.jar_2.mc"; //+
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaB17.jar_1.mc"; //+
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaB18.jar_2.mc";

        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaC1.jar_1.mc"; //+
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaC2.jar_1.mc";
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaC3.jar_1.mc"; //+
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaC3.jar_2.mc"; //+
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaC5.jar_1.mc";
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaC5.jar_2.mc";
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaC7.jar_1.mc"; //+
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaC7.jar_2.mc"; //+
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaC9.jar_1.mc";
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaC10.jar_1.mc";
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PastaC11.jar_1.mc";

        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\PlusSwap.jar_1.mc"; //+

        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\Round3.jar_1.mc"; //really does not terminate
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\Round3.jar_1.mc"; //really does not terminate
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\RunningPointers.jar_1.mc"; //+

        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\Shuffle.jar_1.mc";
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\SortCount.jar_1.mc";
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\StupidArray.jar_1.mc"; //+ no cycles mcg 1 removed
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\StupidArray.jar_2.mc";

        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\Take.jar_1.mc"; //+


        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\GCD.jar_1.mc"; //+ !=
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\GCD.jar_2.mc"; //+ !=
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\GCD2.jar_1.mc"; //+ !=
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\GCD2.jar_2.mc"; //+ succeeded after a few minutes
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\GCD2.jar_3.mc"; //+ removed !=
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\GCD3.jar_1.mc";
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\GCD3.jar_2.mc"; //+ one minute min_min_min ordering
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\GCD4.jar_1.mc";
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\GCD4.jar_2.mc"; //+ one minute min_min_min ordering
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\GCD5.jar_1.mc"; // prolog missed edges
        args[0]="E:\\MSc\\ManyExamples\\mc-jbc_mc\\GCD5.jar_2.mc";


        args[0]="E:\\MSc\\ManyExamples\\mc-jbc-aprove_mc\\Aprove_09SLASHGCD3.jar_1.mc";
        args[0]="E:\\MSc\\ManyExamples\\Samir_results\\tpdb_JBC_mc\\Aprove_09\\Overflow.jar.result.mc";
        args[0]="E:\\MSc\\ManyExamples\\Samir\\tpdb_JBC_mc\\Julia_10_Recursive\\Test6.jar.crs.mc.mc";

        args[0]="E:\\MSc\\ManyExamples\\Exc5.jar.crs.mc.mc";

        args[0]="E:\\MSc\\examples\\Julia_10_IterativeSLASHTriTas.jar_1294276302943450830.itrs_1.clpq.pe.mc";
        args[0]="E:\\MSc\\ManyExamples\\Samir_PE2\\Costa_Julia_09SLASHNested_old.mc";

        args[0]="E:\\MSc\\ManyExamples\\MCGraphs_PE\\termination.pe.mc";
        */
        //        args[0] = "E:\\MSc\\ManyExamples\\tpdb_JBC_java\\Aprove_09_mc\\AProVEMath.jar.crs.mc";
        //        String folder = "E:\\MSc\\ManyExamples\\mc-jbc_mc";
        //        testFolder(folder,true);
        //        if (1==1) return;
        Config.silenceMode();
        final Program pr = Program.create(args[0]);
        pr.findLevelMappings();
        final List<MCGraphMapping> rankingFunction = pr.getMcGraphsMappings();
        if (Config.VERIFICATION && rankingFunction != null) {
            final Verifier ver = new Verifier();
            ver.verify(pr.getInitialMCGraphs(), rankingFunction);
        }

        if (rankingFunction != null) {
            System.out.println("YES");
            System.out.println("Ranking function for " + args[0] + ':');
            int i = 0;
            for (final MCGraphMapping mcgm : rankingFunction) {
                ++i;
                System.out.println("Level Mapping " + i + ':');
                System.out.println(mcgm);
            }
        } else {
            System.out.println("MAYBE");
        }

        /*
                String[] arguments1={"x0","x1","x2"};
                ProgramPoint p=new ProgramPoint("p",arguments1);
                System.out.println(p);

                String[] arguments2={"y0","y1","y2"};
                ProgramPoint q=new ProgramPoint("q",arguments2);
                System.out.println(q);

                String[][] relations={{"x0","y1",">"},{"x1","y2",">"},{"x1","y0",">="}};
                //x0   x1   x2
                //  //\    \
                //y0   Y1   y2

                MCGraph g1 = new MCGraph(p,q,relations);
                System.out.println(g1);


                String[][] relations2={{"x0","y0",">"},{"x0","y1",">"},{"x2","y2",">"}};
                //x0   x1   x2
                // |  \      |
                //y0   Y1   y2

                MCGraph g2 = new MCGraph(p,q,relations2);
                System.out.println(g1);
                System.out.println(g2);

                Program program = new Program();
                program.addMCGraph(g1);
                program.addMCGraph(g2);

                program.findLevelMapping(program.getMCGraphs());
        */
        //        SCCGraph scc = new SCCGraph();
        //        scc.createSCC();
    }

}
