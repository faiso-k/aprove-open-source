package aprove.verification.oldframework.Input.Annotators;

import java.io.*;
import java.util.*;

import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Utility.*;

public class DefaultAnnotator implements PublicAnnotator {
    private Properties props = null;
    private Map<String, Annotator> type2annotator = new HashMap<String, Annotator>();

    @Override
    public AnnotatedInput annotate(TypedInput typedInput) throws SourceException {
        Annotator annotator = this.annotatorFor(typedInput.getLanguage(), typedInput.getHandlingMode());
        return new AnnotatedInput(typedInput, annotator.annotate(typedInput));
    }

    public Annotator annotatorFor(Language lang, HandlingMode mode) {
        String type = lang.toString();
        if (lang == Language.FP && mode == HandlingMode.TheoremProver) {
            type = "TheoremProver";
        }
        return this.getAnnotatorFor(type);
    }

    private Annotator getAnnotatorFor(String type) {
        Annotator annotator = this.type2annotator.get(type);
        if (annotator == null) {
            annotator = this.buildAnnotator(type);
            this.type2annotator.put(type, annotator);
        }
        return annotator;
    }

    private Annotator buildAnnotator(String type) {
        this.loadProperties();
        String aname = this.props.getProperty(type);
        if (aname == null) {
            /* no annotator defined in property file */
            return new TrivialAnnotator();
        } else {
            Class<?> aclass;
            try {
                aclass = Class.forName(aname);
            } catch (ClassNotFoundException e) {
                throw new RuntimeException(e);
            }
            try {
                return (Annotator)aclass.newInstance();
            } catch (InstantiationException e) {
                throw new RuntimeException(e);
            } catch (IllegalAccessException e) {
                throw new RuntimeException(e);
            }
        }
    }

    public void loadProperties() {
        if (this.props != null) {
            return;
        }

        Properties defaultprops = new Properties();
        try {
            PropertyLoader.fromResource(defaultprops, DefaultAnnotator.class, "defaultannotators.properties");
        } catch (IOException e) {
            System.err.println(e.getMessage());
            throw new RuntimeException("Cannot load my default annotators props!");
        }
        this.props = new Properties(defaultprops);
        try {
            PropertyLoader.fromFile(this.props, System.getProperty("user.home")+"/.aprove/defaultannotators.properties");
        } catch (IOException e) {
            // Ignore, user's properties probably don't exist
        }
    }
}
