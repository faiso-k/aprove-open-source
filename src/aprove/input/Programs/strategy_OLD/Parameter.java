package aprove.input.Programs.strategy_OLD;

import java.util.*;
import java.util.regex.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Export.Utility.Export_Util.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Created on 02.12.2004 by marmer
 *
 * @author: Martin Mertens
 * @version $Id$
 */

public class Parameter extends Observable {

    /**
     * An entry of this map corresponds to
     *
     *    <code>key = value[sub-parameters]</code>
     *
     * where key is the key of the map; value Pair.x and sub-parameters Pair.y
     */
    private final Map<String, Pair<String, Parameter>> stringToPair;

    /**
     * Maps those parameters to true which are default parameters.
     *
     * For our normal strategy language, default parameters are those not
     * specified directly in the strategy but in the default.properties file.
     */
    private final Map<String, Boolean> predefinedMap;

    private final static Pattern REGEXP = Pattern.compile("[A-Z[0-9]]");

    private Set<Observer> observers;

    /**
     * The parent parameter.
     *
     * The parent notifies observers/is marked as changed if this Parameter
     * notifies observers/is marked as changed.
     */
    private Parameter parent;

    public Parameter(){
        this.stringToPair = new LinkedHashMap<String,Pair<String,Parameter>>();
        this.predefinedMap = new LinkedHashMap<String, Boolean>();
        this.observers = new LinkedHashSet<Observer>();
    }

    /**
     * Returns the value for this key
     */
    public String getValue(String key) {
        return this.stringToPair.get(key).getKey();
    }

    /**
     * Works like addLink, but replaces a mapping instead of throwing a
     * "double key" exception which is necessary in Passes.
     */
    public void replaceLink(String key, String value, Parameter parameter) {
        this.put(key, value, parameter, false);
    }

    private void put(String key, String value, Parameter parameter, boolean isPredefined) {

        this.stringToPair.put(key, new Pair<String, Parameter>(value, parameter));
        this.predefinedMap.put(key, isPredefined);
        this.setChanged();
        if (parameter != null) {
            parameter.parent = this;
        }
        if (this.parent != null) {
            this.parent.setChanged();
        }
    }

    /**
     * Removes an entry (added with addLink, or put)
     */
    public void removeKey(String key) {
        this.stringToPair.remove(key);
    }


    public String toString(String indent) {
        String ret = indent+ "Parameter with mappings:\n";
        for (String temp: this.stringToPair.keySet()) {
            ret += indent+"  -key "+temp+" pointing to "+this.stringToPair.get(temp).getKey()+" and next Parameter ";
            if (this.stringToPair.get(temp).getValue() == null) {
                ret += "null\n";
            } else {
                ret += "\n    ---> "+this.stringToPair.get(temp).getValue().toString();
            }
        }

        return ret;
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    public String export(Export_Util o) {
        return this.export(o, false);
    }


    public String export(Export_Util o, boolean showDefaults) {

        StringBuffer temp = new StringBuffer();
        boolean removeLast = false;

        for (String key: this.stringToPair.keySet()) {
            if (!this.isPredefined(key) || showDefaults) {
                String k = this.checkQuotationMarks(key)?"\""+key+"\"":key;
                String v = this.checkQuotationMarks(this.getValue(key))?"\""+this.getValue(key)+"\"":this.getValue(key);
                temp.append(k+" = "+o.italic(v));
                if (this.stringToPair.get(key).getValue() != null) {
                    temp.append((this.stringToPair.get(key).getValue()).export(o, showDefaults));
                }
                temp.append(", ");
                removeLast = true;
            }
        }

        if (removeLast) {
            temp = new StringBuffer(temp.substring(0, temp.lastIndexOf(",")));
        }
        if (removeLast) {
            return o.fontcolor("["+temp.toString()+"]", Color.GREEN);
        } else {
            return "";
        }
    }

    private boolean isPredefined(String key) {
        return this.predefinedMap.get(key);
    }

    /**
     *
     * @param string
     * @return if nested content has to be put into quotation
     * marks to be reparsed correctly.
     */
    private boolean checkQuotationMarks(String string) {
        if (string == null) {
            return true;
        }
        if (string.length() == 0) {
            return false;
        }
        String first = string.substring(0,1);
        return !Parameter.REGEXP.matcher(first).matches();
    }

    @Override
    public synchronized void addObserver(Observer observer) {
        this.observers.add(observer);
    }

    @Override
    public synchronized void deleteObserver(Observer observer) {
        this.observers.remove(observer);
    }

    @Override
    public void notifyObservers() {
        for (Observer o : this.observers) {
            o.update(this, null);
        }
        if (this.parent != null) {
            this.parent.notifyObservers();
        }
    }

}
