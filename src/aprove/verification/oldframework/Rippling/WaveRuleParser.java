package aprove.verification.oldframework.Rippling;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.DifferenceUnification.*;
import aprove.verification.oldframework.Logic.Formulas.Visitors.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public  class WaveRuleParser {

    public static Set<WaveRule> generateWaveRules(Rule rule, Program program) throws DifferenceUnificationException{

        Set<WaveRule> waveRules = new LinkedHashSet<WaveRule>();

        Set<Pair<Set<Position>, Set<Position>>> annotations =
                    GroundDifferenceUnification.apply(rule.getLeft(), rule.getRight());

        for(Pair<Set<Position>,Set<Position>> pair : annotations) {
                waveRules.addAll(WaveRuleParser.order(program, pair.x, rule.getLeft(), pair.y, rule.getRight()));
        }

        return waveRules;
    }

    protected static Set<WaveRule> order(Program program, Set<Position> leftAnnotations, AlgebraTerm leftTerm, Set<Position> rightAnnotations, AlgebraTerm rightTerm) {
        Set<WaveRule> returnValue = new LinkedHashSet<WaveRule>();

        PowerSet<Position> leftPowerSet = new PowerSet<Position>(leftAnnotations);
        for (Set<Position> leftInwards : leftPowerSet) {

            Set<Position> leftOutwards = new LinkedHashSet<Position>(leftAnnotations);
            leftOutwards.removeAll(leftInwards);

            PowerSet<Position> rightPowerSet = new PowerSet<Position>(rightAnnotations);
            outer: for (Set<Position> rightInwards : rightPowerSet)  {

                Set<Position> rightOutwards = new LinkedHashSet<Position>(rightAnnotations);
                rightOutwards.removeAll(rightInwards);

                // prevent generation of rules like WF_OUT(plus(WH(X),Y)) -> WF_IN(plus(WH(X),Y))
                for(Position position : leftOutwards) {
                    if(position.size() == 1) {
                        continue outer;
                    }
                }

                for(Position position : rightInwards) {
                    if(position.size() == 1) {
                        continue outer;
                    }
                }

                int outwardsMeasure = WaveRuleParser.measureOutwards(leftTerm, leftOutwards, rightTerm, rightOutwards);
                if ( (outwardsMeasure == 1) || (outwardsMeasure == 0 &&
                    (WaveRuleParser.measureInwards(leftTerm, leftInwards, rightTerm, rightInwards) == 1))) {

                    AlgebraTerm leftWaveTerm  = GenerateAnnotatedFormulaVisitor.apply(leftTerm, program, leftInwards, leftOutwards);
                    AlgebraTerm rightWaveTerm = GenerateAnnotatedFormulaVisitor.apply(rightTerm, program, rightInwards, rightOutwards);

                    returnValue.add(WaveRule.create(leftWaveTerm,rightWaveTerm));

                }

            }
        }
        return returnValue;
    }

    private static int measureOutwards(AlgebraTerm leftTerm, Set<Position> leftOutwards, AlgebraTerm rightTerm, Set<Position> rightOutwards) {

        Pair<Integer[], Integer[] > measure = WaveRuleParser.measure(leftTerm, leftOutwards, rightTerm, rightOutwards);

        for(int index = measure.x.length-1; index >= 0; index--) {

            if(measure.x[index] > measure.y[index]) {
                return 1;
            }

            if(measure.x[index] < measure.y[index]) {
                return -1;
            }
        }

        return 0;
    }

    private static int measureInwards(AlgebraTerm leftTerm, Set<Position> leftInwards, AlgebraTerm rightTerm, Set<Position> rightInwards) {

        Pair< Integer[], Integer[]> measure = WaveRuleParser.measure(leftTerm, leftInwards, rightTerm, rightInwards);

        for(int index=0; index < measure.x.length; index++) {

            if(measure.x[index] > measure.y[index]) {
                return 1;
            }

            if(measure.x[index] < measure.y[index]) {
                return -1;
            }
        }

        return 0;
    }

    private static Pair<Integer[], Integer[]> measure(AlgebraTerm leftTerm, Set<Position> leftAnnotations, AlgebraTerm rightTerm, Set<Position> rightAnnotations) {

        int max = 0;

        for(Position position : leftAnnotations) {
            if(position.size() > max) {
                max = position.size();
            }
        }

        for(Position position : rightAnnotations) {
            if(position.size() > max) {
                max = position.size();
            }
        }


        Integer[] left  = new Integer[max];
        Integer[] right = new Integer[max];

        for(int i=0; i < max; i++) {
            left[i]  = Integer.valueOf(0);
            right[i] = Integer.valueOf(0);
        }

        for(Position position : leftAnnotations) {
            int predecessorSize = position.pred().size();
            left[predecessorSize] = left[predecessorSize] + 1;
        }

        for(Position position : rightAnnotations) {
            int predecessorSize = position.pred().size();
            right[predecessorSize] = right[predecessorSize] + 1;
        }

        return new Pair<Integer[], Integer[]>(left,right);
    }

}
