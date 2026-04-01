package aprove.verification.dpframework.MCSProblem.graphics;
//import java.awt.*;
import java.awt.*;
import java.util.*;
import java.util.List;

import javax.swing.*;               //Import these

import aprove.verification.dpframework.MCSProblem.mcnp.*;

public class Drawer extends JPanel // implements Scrollable
{
    private static final int GRAPGH_HEIGHT = 170;

    private List<MCGraph> _mcGraphs;
    private LevelMapping _levelMapping;
    private String _allMCGraphsIDsString;

    private void evaluateAllMCraphsIDsString()
    {
        this._allMCGraphsIDsString = "";
        for (Iterator<MCGraph> it=this._mcGraphs.iterator(); it.hasNext(); ) {
            String mcgId = it.next().getID();
            this._allMCGraphsIDsString+=mcgId+", ";
        }
    }

    public Drawer(List<MCGraph> mcGraphs,LevelMapping levelMapping)
    {
        this._mcGraphs = mcGraphs;
        this._levelMapping = levelMapping;
        this.evaluateAllMCraphsIDsString();
    }

    public Drawer(List<MCGraph> mcGraphs)
    {
        this._mcGraphs = mcGraphs;
        this._levelMapping = null;
        this.evaluateAllMCraphsIDsString();
    }

    public void drawArrow(int x1, int y1, int x2, int y2, Graphics Obj)
    {
        double beta = Math.PI/10;

        double len = Math.abs(x1-x2);
        double height = Math.abs(y1-y2);

        double l = 10; //Math.sqrt(Math.pow(len,2) + Math.pow(height,2)) / 3;

        double angle1 = Math.atan(len/height) - beta;
        int dx1 = (int)(Math.sin(angle1)*l);
        int dy1 = (int)(Math.cos(angle1)*l);

        double angle2 = Math.atan(len/height)+beta;
        int dx2 = (int)(Math.sin(angle2)*l);
        int dy2 = (int)(Math.cos(angle2)*l);

        Obj.drawLine(x1, y1, x2, y2);
        if (x2>=x1 && y2>=y1) {
            Obj.drawLine(x2-dx1, y2-dy1, x2, y2);
            Obj.drawLine(x2-dx2, y2-dy2, x2, y2);
        } else if (x2>=x1 && y2<y1) {
            Obj.drawLine(x2-dx1, y2+dy1, x2, y2);
            Obj.drawLine(x2-dx2, y2+dy2, x2, y2);
        } else if (x2<x1 && y2>=y1) {
            Obj.drawLine(x2+dx1, y2-dy1, x2, y2);
            Obj.drawLine(x2+dx2, y2-dy2, x2, y2);
        } else if (x2<x1 && y2<y1) {
            Obj.drawLine(x2+dx1, y2+dy1, x2, y2);
            Obj.drawLine(x2+dx2, y2+dy2, x2, y2);
        }
        else {
            throw new RuntimeException("Illegal arrow parameters!");
//        System.out.println(angle+" "+"("+x1+","+y1+")"+"->"+"("+x2+","+y2+")"+"->"+"("+(x2-x)+","+(y2-y)+")");
        }
    }

    public void drawStrictArrow(int x1, int y1, int x2, int y2, Graphics Obj)
    {
        this.drawArrow(x1,y1,x2,y2,Obj);
        if (Math.abs(x1-x2)<3) { //handle vertical arrow
            this.drawArrow(x1-1,y1,x2-1,y2,Obj);
            this.drawArrow(x1+1,y1,x2+1,y2,Obj);
        } else {
            this.drawArrow(x1,y1-1,x2,y2-1,Obj);
            this.drawArrow(x1,y1+1,x2,y2+1,Obj);
        }
    }

     public void drawGraph(MCGraph mcg, int graphNumber, Graphics Obj)  //paint function (essential for graphics)
     {
         this.setBackground(Color.white);  //Make window background black
         this.setSize(500,7000);            //Set window size
         this.setPreferredSize(new Dimension(500,7000));

         int digitWidth=this.getFont().getSize();
         int digitHeight=this.getFont().getSize();

         int blankWidth=80;
         int blankHeight=80;

         Argument[] argsFrom = mcg.getPointFrom().getArguments();
         Argument[] argsTo = mcg.getPointTo().getArguments();

         int xOffset = 100;
         int yOffset = 100 + Drawer.GRAPGH_HEIGHT*graphNumber;

         String fromPointID = mcg.getPointFrom().getID();
         String toPointID = mcg.getPointTo().getID();

         Integer progPointBoundFromNum = null;
         Integer progPointBoundToNum = null;
         Integer progPointStrictFromNum = null;
         Integer progPointStrictToNum = null;

         if (this._levelMapping!=null) {
             progPointBoundFromNum = this._levelMapping.getProgPointBoundNumber(fromPointID);
             progPointBoundToNum = this._levelMapping.getProgPointBoundNumber(toPointID);
             progPointStrictFromNum = this._levelMapping.getProgPointStrictNumber(fromPointID);
             progPointStrictToNum = this._levelMapping.getProgPointStrictNumber(toPointID);
         }

         // low/high sets
         Set<String> strictlyOrderedGraphs=null;
         Set<String> removableGraphs=null;
         Set<String> cutsetGraphs=null;
         Set<Integer> fromHighArgsSet=null;
         Set<Integer> fromLowArgsSet=null;
         Set<Integer> toHighArgsSet=null;
         Set<Integer> toLowArgsSet=null;
         if (this._levelMapping!=null) {
             strictlyOrderedGraphs=this._levelMapping.getStrictOrderedGraphs();
             removableGraphs=this._levelMapping.getRemovableGraphs();
             cutsetGraphs = this._levelMapping.getCutsetGraphs();
             fromHighArgsSet=this._levelMapping.getProgramPointFilteredArgumentsHi(fromPointID);
             fromLowArgsSet=this._levelMapping.getProgramPointFilteredArgumentsLo(fromPointID);
             toHighArgsSet=this._levelMapping.getProgramPointFilteredArgumentsHi(toPointID);
             toLowArgsSet=this._levelMapping.getProgramPointFilteredArgumentsLo(toPointID);
         }

         Obj.drawString(mcg.getID(), 15, yOffset - blankWidth/5);

         Obj.drawString(mcg.getPointFrom().getPointName(), 20, yOffset);
//         if (progPointFromNum!=null)
//             Obj.drawString("["+progPointFromNum+"]", 20, yOffset+15);
         for (int i=0; i<argsFrom.length; i++) {
             int x = xOffset + blankWidth*i;
             int y = yOffset;

             if (this._levelMapping!=null) {
                 if (fromHighArgsSet.contains(i) && fromLowArgsSet.contains(i)) {
                    Obj.setColor(Color.YELLOW);
                } else if (fromHighArgsSet.contains(i)) {
                    Obj.setColor(Color.RED);
                } else if (fromLowArgsSet.contains(i)) {
                    Obj.setColor(Color.GREEN);
                }
                 if (fromHighArgsSet.contains(i) || fromLowArgsSet.contains(i)) {
                     Obj.fillRect(x-4, y-digitHeight, digitWidth+4, digitHeight+2);
                     Obj.setColor(Color.BLACK);
                 }
             }

             Obj.drawRect(x-4, y-digitHeight, digitWidth+4, digitHeight+2);

             //if tagged print tag, else print arg name
             if (this._levelMapping instanceof TaggedLevelMapping) {
                 TaggedLevelMapping asTagged=(TaggedLevelMapping)this._levelMapping;
                 String tag = asTagged.getTag(mcg.getPointFrom().getID(), i);
                 Obj.drawString(tag, x, y);
             } else {
                Obj.drawString(argsFrom[i].toString(), x, y);
            }
         }

         Obj.drawString(mcg.getPointTo().getPointName(), 20, yOffset + blankWidth);
//         if (progPointToNum!=null)
//             Obj.drawString("["+progPointToNum+"]", 20, yOffset + blankWidth+15);
         for (int i=0; i<argsTo.length; i++) {
             int x = xOffset + blankWidth*i;
             int y = yOffset+blankHeight;

             if (this._levelMapping!=null) {
                 if (toHighArgsSet.contains(i) && toLowArgsSet.contains(i)) {
                    Obj.setColor(Color.YELLOW);
                } else if (toHighArgsSet.contains(i)) {
                    Obj.setColor(Color.RED);
                } else if (toLowArgsSet.contains(i)) {
                    Obj.setColor(Color.GREEN);
                }
                 if (toHighArgsSet.contains(i) || toLowArgsSet.contains(i)) {
                     Obj.fillRect(x-4, y-digitHeight, digitWidth+4, digitHeight+2);
                     Obj.setColor(Color.BLACK);
                 }
            }

             Obj.drawRect(x-4, y-digitHeight, digitWidth+4, digitHeight+2);
             //if tagged print tag, else print arg name
             if (this._levelMapping instanceof TaggedLevelMapping) {
                 TaggedLevelMapping asTagged=(TaggedLevelMapping)this._levelMapping;
                 String tag = asTagged.getTag(mcg.getPointTo().getID(), i);
                 Obj.drawString(tag, x, y);
             } else {
                Obj.drawString(argsTo[i].toString(), x, y);
            }
         }

         for (int i=0; i<argsFrom.length; i++) {
             for (int j=0; j<argsTo.length; j++) {
                 int x1 = xOffset + blankWidth*i + digitWidth/2;
                 int x2 = xOffset + blankWidth*j + digitWidth/2;
                 int y1 = yOffset;
                 int y2 = yOffset + blankHeight-digitHeight;
                 if (mcg.getRelation(argsFrom[i],argsTo[j]) !=  null) {
                     if (mcg.getRelation(argsFrom[i],argsTo[j]).equals(">=")) {
                        this.drawArrow(x1, y1, x2, y2,Obj);
                    } else if (mcg.getRelation(argsFrom[i],argsTo[j]).equals(">")) {
                        this.drawStrictArrow(x1, y1, x2, y2,Obj);
                    }
                 }
                 if (mcg.getRelation(argsTo[j],argsFrom[i]) !=  null) {
                     if (mcg.getRelation(argsTo[j],argsFrom[i]).equals(">=")) {
                        this.drawArrow(x2, y2, x1, y1, Obj);
                    } else if (mcg.getRelation(argsTo[j],argsFrom[i]).equals(">")) {
                        this.drawStrictArrow(x2, y2, x1, y1, Obj);
                    }
                 }
             }
         }

         // from -> from
         for (int i=0; i<argsFrom.length; i++) {
             for (int j=0; j<argsFrom.length; j++) {
                 int x1 = xOffset + blankWidth*i + digitWidth/2;
                 int x2 = xOffset + blankWidth*j + digitWidth/2;
                 int y = yOffset-digitHeight;
                 if (mcg.getRelation(argsFrom[i],argsFrom[j]) !=  null) {
                     if (mcg.getRelation(argsFrom[i],argsFrom[j]).equals(">=")) {
                         Obj.drawLine(x1, y, (x1+x2)/2, y-15);
                         this.drawArrow((x1+x2)/2, y-15, x2, y,Obj);
                     } else if (mcg.getRelation(argsFrom[i],argsFrom[j]).equals(">")) {
                         Obj.drawLine(x1, y-1, (x1+x2)/2, y-16);
                         Obj.drawLine(x1, y, (x1+x2)/2, y-15);
                         Obj.drawLine(x1, y+1, (x1+x2)/2, y-14);
                         this.drawStrictArrow((x1+x2)/2, y-15, x2, y,Obj);
                     }
                 }
             }
         }

         // to -> to
         for (int i=0; i<argsTo.length; i++) {
             for (int j=0; j<argsTo.length; j++) {
                 int x1 = xOffset + blankWidth*i + digitWidth/2;
                 int x2 = xOffset + blankWidth*j + digitWidth/2;
                 int y = yOffset+blankHeight;
                 if (mcg.getRelation(argsTo[i],argsTo[j]) !=  null) {
                     if (mcg.getRelation(argsTo[i],argsTo[j]).equals(">=")) {
                         Obj.drawLine(x1, y, (x1+x2)/2, y+15);
                         this.drawArrow((x1+x2)/2, y+15, x2, y,Obj);
                     } else if (mcg.getRelation(argsTo[i],argsTo[j]).equals(">")) {
                         Obj.drawLine(x1, y-1, (x1+x2)/2, y+16);
                         Obj.drawLine(x1, y, (x1+x2)/2, y+15);
                         Obj.drawLine(x1, y+1, (x1+x2)/2, y+14);
                         this.drawStrictArrow((x1+x2)/2, y+15, x2, y,Obj);
                     }
                 }
             }
         }


         Obj.drawRoundRect(10, yOffset-35, Math.max(argsFrom.length, argsTo.length)*blankWidth+50, blankHeight+60,30,30);
         if (this._levelMapping!=null && removableGraphs.contains(mcg.getID())) {
            Obj.drawRect(8, yOffset-37, Math.max(argsFrom.length, argsTo.length)*blankWidth+54, blankHeight+64);
        }
     }


     @Override
    public void paint(Graphics Obj)  //paint function (essential for graphics)
     {
         if (this._levelMapping != null) { //all graphs drawing
             Obj.drawString("Ordering: "+this._levelMapping.getType(), 10, 15);
             Obj.drawString("MC Graphs: "+this._allMCGraphsIDsString, 10, 30);
         }
         int i=0;
         for (Iterator<MCGraph> it=this._mcGraphs.iterator(); it.hasNext(); i++) {
             MCGraph mcg = it.next();
             this.drawGraph(mcg,i,Obj);
         }
     }

//     public static MCGraph getGraph()
//     {
//         String[] arguments1={"x0","x1","x2"};
//        ProgramPoint p=new ProgramPoint("p",arguments1);
//        String[] arguments2={"y0","y1","y2"};
//        ProgramPoint q=new ProgramPoint("q",arguments2);
//        String[][] relations={{"x0","y1",">"},{"x1","y2",">"},{"x1","y0",">="},{"y0","x2",">"},{"x1","x2",">"},{"x2","x0",">="},{"y0","y2",">"}};
//        MCGraph g = new MCGraph(p,q,relations);
//        return g;
//    }
}