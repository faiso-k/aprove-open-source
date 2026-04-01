package aprove.verification.oldframework.Utility;

public class ASCII {
   public static final String[] escapeSequences =
   new String[]{"\\NUL", "\\SOH", "\\STX", "\\ETX",
                "\\EOT", "\\ENQ", "\\ACK", "\\BEL",
                "\\BS",  "\\HT",  "\\LF" , "\\VT" ,
                "\\FF" , "\\CR",  "\\SO",  "\\SI",
                "\\DLE", "\\DC1", "\\DC2", "\\DC3",
                "\\DC4", "\\NAK", "\\SYN", "\\ETB",
                "\\CAN", "\\EM",  "\\SUB", "\\ESC",
                "\\FS",  "\\GS",  "\\RS",  "\\US",
                "\\SP",                                // Space =  Index 32
                "",
                "\\\"", "","","","",                   // \" = 34
                "\\'",                                 // \' = 39
                "\\a",   "\\b",   "\\t",   "\\n",      // \a = 7  index 40
                "\\v",   "\\f",   "\\r",
                "\\&",                                 // EmptyChar index 47
                "\\\\",                                // \\ = 92   index 48
                "\\DEL" };                             // \DEL = 127 index 49


   /**
    * returns the number of the character representet by the given escape sequence
    * -1 empty character or gap(ignored blanks,tabs, returns, newlines);
    * -2 invalid escape sequence
    */
   public static final int escapeToInt(String t){
       if (t.startsWith("\\")) {
           if (t.startsWith("\\x")) {
               String spe = t.substring(2,t.length());
               try {
                return Integer.parseInt(spe,16);
           } catch (Exception e){
            return -2;
           }

       }
           if (t.startsWith("\\^")) {
               int i = "@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_".indexOf(t.charAt(2));
               if (i<0) {
                return -2;
            }
           return i;
           } else {
           boolean ok = true;
           for (int i=1;i<t.length();i++){
              int l = "0123456789".indexOf(t.charAt(i));
          if (l<0) { ok = false;}
           }
               String spe = t.substring(1,t.length());
           if (ok) {
              try {
                 return Integer.parseInt(spe);
          } catch (Exception e){
             return -2;
          }
           }
       }
           for (int i=0;i<ASCII.escapeSequences.length;i++){
               if (ASCII.escapeSequences[i].equals(t)) {
                   if (i<40) {
                    return i;
                }
                   if (i<47) {
                    return i-40+7;
                }
                   if (i == 47) {
                    return -1;
                }
                   if (i == 48) {
                    return 92;
                }
                   if (i == 49) {
                    return 127;
                }
               }
           }
           String sp = t.substring(1,t.length());
           if (t.charAt(t.length()-1) =='\\') {
              for (int i = 0;i<sp.length();i++){
                 if (("\n\t\r ".indexOf(sp.charAt(i))) == -1) {
                    return -2;
                }
              }
              return -1;
           }
           return -2;
       } else {
           return t.charAt(0);
       }
   }
}
