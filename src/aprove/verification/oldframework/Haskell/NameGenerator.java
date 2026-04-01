package aprove.verification.oldframework.Haskell;

import java.util.*;
 /**
 * @author Stephan Swiderski
 * @version $Id$
 *
 *
 * a NameGenerator creates new Names for some Objects
 * and returns the same name for this object by collecting this relations
 * in a map
 * by overloading the method createNewNameFor which is called only once per object
 * the name could be created
 */
public abstract class NameGenerator{
   Map<Object,String> nameMap;

   public NameGenerator(){
       this.nameMap = new HashMap<Object,String>();
   }

   public String getNameFor(Object o){
       String name = (this.nameMap.get(o));
       if (name == null) {
           name = this.createNewNameFor(o);
           this.nameMap.put(o,name);
       }
       return name;
   }

   public abstract String createNewNameFor(Object o);

}
