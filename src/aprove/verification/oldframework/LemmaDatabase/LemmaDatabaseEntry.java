package aprove.verification.oldframework.LemmaDatabase;

import java.io.*;
import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;

public class LemmaDatabaseEntry implements HTML_Able {

    protected long  primaryKey;

    File  file;

    protected Formula   formula;

    protected Map<DefFunctionSymbol, Set<Rule>> rules;

    protected Set<Sort> sorts;

    public LemmaDatabaseEntry() {
        super();
    }

    public LemmaDatabaseEntry(long primarykey, File file, Formula formula, Map<DefFunctionSymbol,Set<Rule>> rules, Set<Sort> typeDefinitions) {
        this.primaryKey = primarykey;
        this.formula     = formula;
        this.rules         = rules;
        this.sorts         = typeDefinitions;
    }

    public Formula getFormula() {
        return this.formula;
    }

    public void setFormula(Formula formula) {
        this.formula = formula;
    }

    public Map<DefFunctionSymbol,Set<Rule>> getRules() {
        return this.rules;
    }

    public void setRules(Map<DefFunctionSymbol,Set<Rule>> rules) {
        this.rules = rules;
    }

    public Set<Sort> getSorts() {
        return this.sorts;
    }

    public void setSorts(Set<Sort> sorts) {
        this.sorts = sorts;
    }

    @Override
    public String toHTML() {

        HTML_Util htmlUtil = new HTML_Util();

        StringBuffer stringBuffer = new StringBuffer();

        // show formula
        stringBuffer.append( htmlUtil.bold("Formula:"));
        stringBuffer.append(htmlUtil.newline());
        stringBuffer.append(this.formula.toHTML());
        stringBuffer.append(htmlUtil.newline());
        stringBuffer.append(htmlUtil.newline());

        // show rules
        stringBuffer.append( htmlUtil.bold("Rules:"));
        stringBuffer.append(htmlUtil.newline());
        for(Set<Rule> setOfRules : this.rules.values()) {
            for(Rule rule : setOfRules) {
                stringBuffer.append(rule.toHTML());
                stringBuffer.append(htmlUtil.newline());
            }
        }
        stringBuffer.append( htmlUtil.newline());

        // show data typedefinitions
        stringBuffer.append( htmlUtil.bold("Sorts:"));
        stringBuffer.append(htmlUtil.newline());
        for(Sort typeDefinition : this.sorts) {
            stringBuffer.append(typeDefinition.toString());
            stringBuffer.append(htmlUtil.newline());
        }

        return stringBuffer.toString();
    }

    public long getPrimaryKey() {
        return this.primaryKey;
    }

    public void setPrimaryKey(long primaryKey) {
        this.primaryKey = primaryKey;
    }

}
