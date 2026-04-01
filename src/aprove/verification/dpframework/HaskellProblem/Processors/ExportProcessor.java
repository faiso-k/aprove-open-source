package aprove.verification.dpframework.HaskellProblem.Processors;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.HaskellProblem.*;
import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Modules.HaskellEntity.*;
import aprove.verification.theoremprover.TerminationProofs.*;
@NoParams
public class ExportProcessor extends HaskellProcessor {

    @Override
    protected Set<Class<? extends HaskellProcessor>> getPreconditionTransformations(
            HaskellProgram hp) {
        // TODO Auto-generated method stub
        return new LinkedHashSet<Class<? extends HaskellProcessor>>();
    }

    @Override
    public Result process(HaskellProgram obl, Abortion aborter)
            throws AbortionException {
        // TODO Auto-generated method stub

        try {
        //FileWriter fw = new FileWriter(Main.getHaskellTransformationOutput());
        obl = obl.deepcopy();
        Modules modules = obl.getModules();
        Prelude prelude = modules.getPrelude();
        TyConsEntity boolEntity = prelude.getBool();
        ConsEntity boolTrue = prelude.getBoolTrue();
        ConsEntity boolFalse = prelude.getBoolFalse();
        HaskellNamedSym boolSym = prelude.getBoolSym();
        boolSym.setName("MyBool");
        boolTrue.setName("MyTrue");
        boolFalse.setName("MyFalse");
        boolEntity.setName("MyBool");
        TyConsEntity intEntity= (TyConsEntity) prelude.getEntityN(null, "", "Int", Sort.TYCONS);
        if (intEntity != null) {
            intEntity.setName("MyInt");
        }
        TyConsEntity listEntity = prelude.getList();
        ConsEntity listCons = prelude.getListCons();
        ConsEntity listNil = prelude.getListNil();
        listCons.setName("Cons");
        listNil.setName("Nil");
        listEntity.setName("List");
        prelude.removeEntity(prelude.getEntity(null,"","terminator",Sort.VAR));
        //prelude.removeEntity(prelude.getEntity(null,"","error",Sort.VAR));




        //fw.append(obl.toBasicPLAIN());
        //fw.close();
        System.out.println(obl.toBasicPLAIN());
        } catch (Exception e){
            System.err.println(e.getMessage());
            e.printStackTrace();

        }



        return ResultFactory.proved(new EmptyProof("Haskellprogram Exported"));
    }

}
