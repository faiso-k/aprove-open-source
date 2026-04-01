package aprove.verification.oldframework.LemmaDatabase;

public class LemmaDatabaseFactory {

    private static LemmaDatabase lemmaDatabase;

    public static LemmaDatabase getLemmmaDatabase() {
        if( LemmaDatabaseFactory.lemmaDatabase == null) {
            LemmaDatabaseFactory.lemmaDatabase = new LemmaDatabase();
        }
        return LemmaDatabaseFactory.lemmaDatabase;
    }

}
