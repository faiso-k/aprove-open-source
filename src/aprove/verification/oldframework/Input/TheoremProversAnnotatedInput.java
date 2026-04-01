/*
 * Created on 21.07.2004
 *
 */
package aprove.verification.oldframework.Input;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Input.Annotations.*;

/**
 * @author rabe
 *
 */
public class TheoremProversAnnotatedInput extends AnnotatedInput {

    public TheoremProversAnnotatedInput(TypedInput typedInput, Annotation annotation) {
        super(typedInput, annotation);
    }



    @Override
    public String toHTML() {

        StringBuffer              stringBuffer;
        HTML_Able              htmlAble;
        FormulaAnnotation formulaAnnotation;

        stringBuffer = new StringBuffer();

        stringBuffer.append("<b>");

        if( this.typedInput != null ) {

            if( this.typedInput.getInput() instanceof HTML_Able ) {

                htmlAble = (HTML_Able)this.typedInput.getInput();

                stringBuffer.append(htmlAble.toHTML());

            }

            stringBuffer.append("<br>");

            if( this.annotation instanceof FormulaAnnotation ) {

                formulaAnnotation = (FormulaAnnotation)this.annotation;

                stringBuffer.append(formulaAnnotation.toHTML());
            }

           stringBuffer.append("</b>");

            return stringBuffer.toString();

        } else {

            return "";

        }
    }
}
