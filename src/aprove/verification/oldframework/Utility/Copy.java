package aprove.verification.oldframework.Utility;

import java.io.*;
import java.util.*;

public class Copy {

    public static Object copyObject(Object obj) {
        ByteArrayOutputStream baos = new ByteArrayOutputStream();
        try {
            ObjectOutputStream out = new ObjectOutputStream(baos);
            out.writeObject(obj);
            out.close();
        } catch (IOException e) {
            throw new RuntimeException("internal error: object could not be serialized: "+e.getMessage()); //should not happen
        }
        Object newObj;
        ByteArrayInputStream bais = new ByteArrayInputStream(baos.toByteArray());
        try {
            ObjectInputStream in = new ObjectInputStream(bais);
            newObj = in.readObject();
            in.close();
        } catch(Exception e) {
            throw new RuntimeException("internal error: object could not be deserialized: "+e.getMessage()); //should not happen
        }
        return newObj;
    }

    /**
     * Type safe version of copyObject.
     * @return
     */
    @SuppressWarnings("unchecked")
    public static <E> E copyTypesafe(E obj) {
        return (E)Copy.copyObject(obj);
    }


   public static <E extends Deepcopy> E deep(E dc){
       if (dc == null) {
        return null;
    }
       E target = (E) dc.deepcopy();
       if (Copy.copyMap != null){
           Copy.copyMap.put(target,dc);
       }
       return target;
   }

   public static <E extends Deepcopy,S extends Collection<E>> S deepCol(S source){
         if (source == null) {
            return null;
        }
         try {
            Class<Collection> c = (Class<Collection>)source.getClass();
            Collection target = c.newInstance();
            for (E elem : source){
                target.add(Copy.deep(elem));
            }
            if (Copy.copyMap != null){
                Copy.copyMap.put(target,source);
            }
            return (S) target;
         } catch (Exception e){
             throw new RuntimeException(e);
         }
   }

   public static <E extends Deepcopy,T extends Collection<? super E>> T deepCol(T target,Collection<E> source){
        if (source == null) {
            return null;
        }
        for (E elem : source){
           target.add(Copy.deep(elem));
        }
        if (Copy.copyMap != null){
            Copy.copyMap.put(target,source);
        }
        return target;
   }

   public static Map copyMap = null;

}
