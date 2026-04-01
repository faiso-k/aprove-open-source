package aprove.xml.Nodes;

import aprove.xml.*;

public class HaskellElement extends AproveDOMElement {

    public static final HaskellElement Name        = new HaskellElement("Name");
    public static final HaskellElement Apply       = new HaskellElement("Apply");
    public static final HaskellElement Var         = new HaskellElement("Var");
    public static final HaskellElement Cons        = new HaskellElement("Cons");
    public static final HaskellElement Term        = new HaskellElement("Term");
    public static final HaskellElement Arrow       = new HaskellElement("Arrow");
    public static final HaskellElement Tuple       = new HaskellElement("Tuple");
    public static final HaskellElement Let         = new HaskellElement("Let");
    public static final HaskellElement Where       = new HaskellElement("Where");
    public static final HaskellElement Locals      = new HaskellElement("Locals");
    public static final HaskellElement Lambda      = new HaskellElement("Lambda");
    public static final HaskellElement Guard       = new HaskellElement("Guard");
    public static final HaskellElement Condition   = new HaskellElement("Condition");
    public static final HaskellElement Conditions  = new HaskellElement("Conditions");
    public static final HaskellElement If          = new HaskellElement("If");
    public static final HaskellElement Case        = new HaskellElement("Case");
    public static final HaskellElement Alt         = new HaskellElement("Alt");
    public static final HaskellElement Pattern     = new HaskellElement("Pattern");
    public static final HaskellElement PlusPat     = new HaskellElement("PlusPat");
    public static final HaskellElement IrrPat      = new HaskellElement("IrrPat");
    public static final HaskellElement JokerPat    = new HaskellElement("JokerPat");
    public static final HaskellElement Char        = new HaskellElement("Char");
    public static final HaskellElement Int         = new HaskellElement("Int");
    public static final HaskellElement Float       = new HaskellElement("Float");
    public static final HaskellElement BindPat     = new HaskellElement("BindPat");
    public static final HaskellElement Rule        = new HaskellElement("Rule");
    public static final HaskellElement Function    = new HaskellElement("Function");
    public static final HaskellElement PatDecl     = new HaskellElement("PatDecl");
    public static final HaskellElement InfixDecl   = new HaskellElement("InfixDecl");
    public static final HaskellElement Decls       = new HaskellElement("Decls");
    public static final HaskellElement HClass      = new HaskellElement("Class");
    public static final HaskellElement HClasses    = new HaskellElement("Classes");
    public static final HaskellElement Members     = new HaskellElement("Members");
    public static final HaskellElement Instance    = new HaskellElement("Instance");
    public static final HaskellElement Instances   = new HaskellElement("Instances");
    public static final HaskellElement DataType    = new HaskellElement("DataType");
    public static final HaskellElement NewType     = new HaskellElement("NewType");
    public static final HaskellElement DataTypes   = new HaskellElement("DataTypes");
    public static final HaskellElement Constr      = new HaskellElement("Constr");
    public static final HaskellElement Constraint  = new HaskellElement("Constraint");
    public static final HaskellElement Constraints = new HaskellElement("Constraints");
    public static final HaskellElement ClassName   = new HaskellElement("ClassName");
    public static final HaskellElement Type        = new HaskellElement("Type");
    public static final HaskellElement TypeBinding = new HaskellElement("TypeBinding");
    public static final HaskellElement TypeSchema  = new HaskellElement("TypeSchema");
    public static final HaskellElement Default     = new HaskellElement("Default");
    public static final HaskellElement Derivings   = new HaskellElement("Derivings");
    public static final HaskellElement Module      = new HaskellElement("Module");
    public static final HaskellElement MainModule  = new HaskellElement("MainModule");
    public static final HaskellElement Imports     = new HaskellElement("Imports");
    public static final HaskellElement Import      = new HaskellElement("Import");
    public static final HaskellElement Qualified   = new HaskellElement("Qualified");
    public static final HaskellElement List        = new HaskellElement("List");
    public static final HaskellElement Strict      = new HaskellElement("Strict");
    public static final HaskellElement TypeAnno    = new HaskellElement("TypeAnno");
    public static final HaskellElement StartTerm   = new HaskellElement("StartTerm");

    public HaskellElement(String tagName){
            super(tagName);
    }

    public static class FixityAttribute extends AproveDOMAttribute{
        public static final FixityAttribute infix = new FixityAttribute("infix");
        public static final FixityAttribute priority = new FixityAttribute("priority");
        public static final String Value_Left = "Left";
        public static final String Value_Right = "Right";
        public static final String Value_Non = "Non";

        public FixityAttribute(String attName){
                super(attName);
        }

    }

}
