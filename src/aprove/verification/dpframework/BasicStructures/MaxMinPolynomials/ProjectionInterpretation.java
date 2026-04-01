package aprove.verification.dpframework.BasicStructures.MaxMinPolynomials;

import java.util.*;

public class ProjectionInterpretation implements InterpretLabelling{
   private int pos;

   private static final Map<Integer, ProjectionInterpretation> projMap = new LinkedHashMap<Integer, ProjectionInterpretation>();

   public static ProjectionInterpretation create(int position) {
       ProjectionInterpretation result = ProjectionInterpretation.projMap.get(position);
       if(result == null) {
           result = new ProjectionInterpretation(position);
           ProjectionInterpretation.projMap.put(position, result);
       }
       return result;
   }

   private ProjectionInterpretation(int position) {
        this.pos = position;
    }

    @Override
    public MaxMinPolynomial interpret (MaxMinPolynomial mmp1, MaxMinPolynomial mmp2) {
        return (this.pos==0) ? mmp1 : mmp2;
    }

    @Override
    public boolean equals(Object object) {
        //singleton property
        return this == object;
    }

    @Override
    public int hashCode() {
        // singleton property
        return super.hashCode();
    }

    @Override
    public String toString() {
        return ("Proj_on " + (this.pos +1));
    }

    @Override
    public InterpretLabelling getInterpretation (int pos) {
        return this;
    }

}
