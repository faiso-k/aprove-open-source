package aprove.verification.oldframework.Input.Annotations;


public class NewPrologAnnotation extends Annotation {
    //    List<String> queries;
    private final String query;

    public NewPrologAnnotation() {
        //        this.queries = null;
        this.query = null;
    }

    public NewPrologAnnotation(final String q) {
        if (!q.startsWith("%query") && !q.startsWith("%complexity") && !q.startsWith("%determinacy")) {
            // The given query doesn't specify the goal of the analysis. Default to termination.
            this.query = "%query: " + q;
        } else {
            this.query = q;
        }
    }

    //    public NewPrologAnnotation(List<String> startTerms){
    //
    //        this.queries = new ArrayList<String>();
    //        for (String protoQuery : startTerms) {
    //            String query = "%query: "+protoQuery;
    //            this.queries.add(query);
    //        }
    //    }

    //    public List<String>getQueries(){
    //        return this.queries;
    //    }

    public String getQuery() {
        return this.query;
    }

}
