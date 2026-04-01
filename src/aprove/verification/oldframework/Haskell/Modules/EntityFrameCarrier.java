package aprove.verification.oldframework.Haskell.Modules;

import aprove.verification.oldframework.Haskell.*;

/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * Module, LetExp, Lambda, AltExp are EntityFrameCarrier
 * and this interface offers the view to thier EntityFrame
 */

public interface EntityFrameCarrier extends HaskellObject {

     public void setEntityFrame(EntityFrame entityFrame);

     public EntityFrame getEntityFrame();

}