package aprove.verification.oldframework.LemmaDatabase;

import aprove.verification.oldframework.Logic.Formulas.*;

public interface LemmaDatabaseUpdateListener {

    enum Type { ADD, REMOVE, REMOVE_ALL };
    public void lemmaDatabaseUpdated(LemmaDatabase source, Type type, Formula lemma);

}
