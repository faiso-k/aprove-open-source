package aprove.verification.oldframework.Input.Annotations;
import java.util.*;

public class HaskellAnnotation extends Annotation{
     List<String> startTerms;

     public HaskellAnnotation(){
         this.startTerms = null;
     }


     public HaskellAnnotation(List<String> startTerms){
         this.startTerms = startTerms;
     }

     public List<String>getStartTerms(){
         return this.startTerms;
     }
}


