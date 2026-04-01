<xsl:stylesheet version="1.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform">
<xsl:output method="text"/>

<xsl:template match="/">
<xsl:apply-templates />
</xsl:template>

<xsl:template match="Term" >
    <xsl:param name = "Second" />
    <xsl:param name = "Priority" />
    <xsl:param name = "Fixity" />
    <xsl:param name = "Pos" />
	<xsl:apply-templates select="Var|Apply|Cons|Let|If|TypeBinding|Conditions|Int|Char|Float|Lambda|Case|PlusPat|JokerPat|BindPat|IrrPat|InfixDecl|Tuple|Where|Strict">
       <xsl:with-param name = "Second" >
         <xsl:value-of select = "$Second"/>
       </xsl:with-param>
       <xsl:with-param name = "Priority" >
         <xsl:value-of select = "$Priority"/>
       </xsl:with-param>
       <xsl:with-param name = "Fixity" >
         <xsl:value-of select = "$Fixity"/>
       </xsl:with-param>
       <xsl:with-param name = "Pos" >
         <xsl:value-of select = "$Pos"/>
       </xsl:with-param>
    </xsl:apply-templates>
</xsl:template>

<xsl:template match="Term[count(Apply/Term[1]/Cons/List)>0]" priority ="5">
    <xsl:text>[</xsl:text>
    <xsl:apply-templates select="Apply/Term[2]"/>
    <xsl:text>]</xsl:text>
</xsl:template>

<xsl:template match="Term[count(Apply/Term[1]/Apply/Term[1]/Cons[@infix])>0]" priority ="5">
    <xsl:param name = "Second" />
    <xsl:param name = "Priority" />
    <xsl:param name = "Fixity" />
    <xsl:param name = "Pos" />

    <xsl:if test="($Second = &quot;true&quot; or Apply/Term[1]/Apply/Term[1]/Cons/@priority &lt; $Priority) or
                    ((Apply/Term[1]/Apply/Term[1]/Cons/@priority=$Priority) and
                    (not(Apply/Term[1]/Apply/Term[1]/Cons/@infix=$Pos) or
                     not(Apply/Term[1]/Apply/Term[1]/Cons/@infix=$Fixity)
                      or Apply/Term[1]/Apply/Term[1]/Cons/@infix=&quot;Non&quot;))">
      <xsl:text>(</xsl:text>
    </xsl:if>

    <xsl:apply-templates select="Apply/Term[1]/Apply/Term[2]">
       <xsl:with-param name = "Pos" >Left</xsl:with-param>
       <xsl:with-param name = "Priority" >
       <xsl:value-of select="Apply/Term[1]/Apply/Term[1]/Cons/@priority" /></xsl:with-param>
       <xsl:with-param name = "Fixity" >
          <xsl:value-of select="Apply/Term[1]/Apply/Term[1]/Cons/@infix" />
       </xsl:with-param>
    </xsl:apply-templates>
      <xsl:text> </xsl:text>
	<xsl:apply-templates select="Apply/Term[1]/Apply/Term[1]/Cons"/>
      <xsl:text> </xsl:text>

    <xsl:apply-templates select="Apply/Term[2]">
       <xsl:with-param name = "Pos" >Right</xsl:with-param>
       <xsl:with-param name = "Priority" >
          <xsl:value-of select="Apply/Term[1]/Apply/Term[1]/Cons/@priority" />
       </xsl:with-param>
       <xsl:with-param name = "Fixity" >
          <xsl:value-of select="Apply/Term[1]/Apply/Term[1]/Cons/@infix" />
       </xsl:with-param>
    </xsl:apply-templates>

    <xsl:if test="($Second = &quot;true&quot; or Apply/Term[1]/Apply/Term[1]/Cons/@priority &lt; $Priority) or
                    ((Apply/Term[1]/Apply/Term[1]/Cons/@priority=$Priority) and
                    (not(Apply/Term[1]/Apply/Term[1]/Cons/@infix=$Pos) or
                     not(Apply/Term[1]/Apply/Term[1]/Cons/@infix=$Fixity)
                      or Apply/Term[1]/Apply/Term[1]/Cons/@infix=&quot;Non&quot;))">
      <xsl:text>)</xsl:text>
    </xsl:if>
</xsl:template>

<xsl:template match="Term[count(Apply/Term[1]/Apply/Term[1]/Var[@infix])>0]" priority ="5">
    <xsl:param name = "Second" />
    <xsl:param name = "Priority" />
    <xsl:param name = "Fixity" />
    <xsl:param name = "Pos" />

    <xsl:if test="$Second = &quot;true&quot; or (Apply/Term[1]/Apply/Term[1]/Var/@priority &lt; $Priority) or
                    ((Apply/Term[1]/Apply/Term[1]/Var/@priority=$Priority) and
                    (not(Apply/Term[1]/Apply/Term[1]/Var/@infix=$Pos) or
                     not(Apply/Term[1]/Apply/Term[1]/Var/@infix=$Fixity)
                      or Apply/Term[1]/Apply/Term[1]/Var/@infix=&quot;Non&quot;))">
      <xsl:text>(</xsl:text>
    </xsl:if>

    <xsl:apply-templates select="Apply/Term[1]/Apply/Term[2]">
       <xsl:with-param name = "Pos" >Left</xsl:with-param>
       <xsl:with-param name = "Priority" >
          <xsl:value-of select="Apply/Term[1]/Apply/Term[1]/Var/@priority" />
       </xsl:with-param>
       <xsl:with-param name = "Fixity" >
          <xsl:value-of select="Apply/Term[1]/Apply/Term[1]/Var/@infix" />
       </xsl:with-param>
    </xsl:apply-templates>
      <xsl:text> </xsl:text>
	<xsl:apply-templates select="Apply/Term[1]/Apply/Term[1]/Var"/>
      <xsl:text> </xsl:text>

    <xsl:apply-templates select="Apply/Term[2]">
       <xsl:with-param name = "Pos" >Right</xsl:with-param>
       <xsl:with-param name = "Priority" >
          <xsl:value-of select="Apply/Term[1]/Apply/Term[1]/Var/@priority" />
       </xsl:with-param>
       <xsl:with-param name = "Fixity" >
          <xsl:value-of select="Apply/Term[1]/Apply/Term[1]/Var/@infix" />
       </xsl:with-param>
    </xsl:apply-templates>

    <xsl:if test="($Second = &quot;true&quot; or Apply/Term[1]/Apply/Term[1]/Var/@priority &lt; $Priority) or
                    ((Apply/Term[1]/Apply/Term[1]/Var/@priority=$Priority) and
                    (not(Apply/Term[1]/Apply/Term[1]/Var/@infix=$Pos) or
                     not(Apply/Term[1]/Apply/Term[1]/Var/@infix=$Fixity)
                      or Apply/Term[1]/Apply/Term[1]/Var/@infix=&quot;Non&quot;))">
      <xsl:text>)</xsl:text>
    </xsl:if>
</xsl:template>

<xsl:template match="Var">
	<xsl:apply-templates select="Name"/>
</xsl:template>

<xsl:template match="Apply">
    <xsl:param name = "Second" />
    <xsl:if test="$Second=&quot;true&quot;">
      <xsl:text>(</xsl:text>
    </xsl:if>
    <xsl:apply-templates select="Term[1]">
       <xsl:with-param name = "Pos" >Left</xsl:with-param>
       <xsl:with-param name = "Priority" >10</xsl:with-param>
       <xsl:with-param name = "Fixity" >Left</xsl:with-param>
    </xsl:apply-templates>            
	<xsl:text> </xsl:text>
	<xsl:apply-templates select="Term[2]">
       <xsl:with-param name = "Second" >true</xsl:with-param>
    </xsl:apply-templates>
    <xsl:if test="$Second=&quot;true&quot;">
      <xsl:text>)</xsl:text>
    </xsl:if>
</xsl:template>

<xsl:template match="Guard">
    <xsl:apply-templates select="Term" />
</xsl:template>

<xsl:template match="Char">
	<xsl:text>'</xsl:text>
    <xsl:apply-templates select="text()" />
	<xsl:text>'</xsl:text>
</xsl:template>

<xsl:template match="Int">
    <xsl:apply-templates select="text()" />
</xsl:template>

<xsl:template match="JokerPat">
    <xsl:text>_</xsl:text>
</xsl:template>

<xsl:template match="BindPat">
    <xsl:apply-templates select="Var" />
    <xsl:text>@</xsl:text>
	<xsl:apply-templates select="Term">
       <xsl:with-param name = "Second" >true</xsl:with-param>
    </xsl:apply-templates>
</xsl:template>

<xsl:template match="Strict">
    <xsl:text>!</xsl:text>
    <xsl:apply-templates select="Term" />
</xsl:template>

<xsl:template match="IrrPat">
    <xsl:text>&#126;(</xsl:text>
    <xsl:apply-templates select="Term" />
    <xsl:text>)</xsl:text>
</xsl:template>

<xsl:template match="PlusPat">
    <xsl:text>(</xsl:text>
    <xsl:apply-templates select="Term[1]" />
    <xsl:text>+</xsl:text>
    <xsl:apply-templates select="Term[2]" />
    <xsl:text>)</xsl:text>
</xsl:template>

<xsl:template match="ClassName">
    <xsl:apply-templates select="text()" />
</xsl:template>

<xsl:template match="Float">
    <xsl:apply-templates select="text()" />
</xsl:template>

<xsl:template match="Condition">
   <xsl:param name = "Arrow" />
   <xsl:param name = "Where" />
   <xsl:text> | </xsl:text>
   <xsl:apply-templates select="Guard" />
   <xsl:text> </xsl:text>
   <xsl:value-of select="$Arrow"/>
   <xsl:text> </xsl:text>
   <xsl:apply-templates select="Term" />
   <xsl:if test="($Where=&quot;true&quot;)">
       <xsl:apply-templates select="../../../Where" mode="noexp"/>
   </xsl:if>
   <xsl:if test="not($Where=&quot;true&quot;)">
       <xsl:text>&#10;</xsl:text>
   </xsl:if>   
</xsl:template>

<xsl:template match="Conditions">
   <xsl:param name = "Arrow" />
   <xsl:for-each select="Condition">
     	<xsl:if test="(position() = 1)">
		   <xsl:apply-templates select="." >
		   <xsl:with-param name = "Arrow" ><xsl:value-of select="$Arrow"/></xsl:with-param>
              <xsl:with-param name = "Where" ><xsl:if test="(position() = last())">true</xsl:if></xsl:with-param>
           </xsl:apply-templates>
		</xsl:if>
     	<xsl:if test="not(position() = 1)">
		   <xsl:apply-templates select="." >
		   <xsl:with-param name = "Arrow" ><xsl:value-of select="$Arrow"/></xsl:with-param>
              <xsl:with-param name = "Where" ><xsl:if test="(position() = last())">true</xsl:if></xsl:with-param>
           </xsl:apply-templates>
		</xsl:if>
  </xsl:for-each>
</xsl:template>

<xsl:template match="Alt">
   <xsl:apply-templates select="Pattern/Term" />
   <xsl:if test="(count(Conditions) = 0) and (count(Term/Where/Conditions) = 0)">
       <xsl:text>-> </xsl:text>
       <xsl:apply-templates select="Term"/>
   </xsl:if>
   <xsl:if test="(count(Conditions) = 1) ">
     <table cellspacing="0" cellpadding="0" border="0" frame="void" >
     <xsl:apply-templates select="Conditions">
        <xsl:with-param name = "Arrow" ><xsl:text>-></xsl:text></xsl:with-param>
     </xsl:apply-templates>
     </table>
   </xsl:if>
  <xsl:if test="(count(Term/Where/Conditions) = 1)">
     <table cellspacing="0" cellpadding="0" border="0" frame="void" >
     <xsl:apply-templates select="Term/Where/Conditions">
        <xsl:with-param name = "Arrow" ><xsl:text>-></xsl:text></xsl:with-param>
     </xsl:apply-templates>
     </table>
   </xsl:if>
   <xsl:text>; &#10;</xsl:text>
</xsl:template>

<xsl:template match="Case">
    <xsl:param name = "Second" />
    <xsl:if test="$Second=&quot;true&quot;">
      <xsl:text>(</xsl:text>
    </xsl:if>
   <xsl:text>case </xsl:text>
   <xsl:apply-templates select="Term" />
   <xsl:text> of { &#10;</xsl:text>
   <xsl:for-each select="Alt">
   <xsl:apply-templates select="."/>
   </xsl:for-each>
   <xsl:text> } </xsl:text>
    <xsl:if test="$Second=&quot;true&quot;">
      <xsl:text>)</xsl:text>
    </xsl:if>
</xsl:template>

<xsl:template match="TypeBinding">
	<xsl:text>(</xsl:text>
	<xsl:apply-templates select="Term">
        <xsl:with-param name = "Second" >true</xsl:with-param>
        </xsl:apply-templates>
	<xsl:text> :: </xsl:text>
	<xsl:apply-templates select="TypeSchema" />
	<xsl:text>)</xsl:text>
</xsl:template>

<xsl:template match="Lambda">
	<xsl:text>(</xsl:text>
	<xsl:text>\</xsl:text>
    <xsl:apply-templates select="Pattern" />
	<xsl:text>-&gt;</xsl:text>
	<xsl:apply-templates select="Term" />
	<xsl:text>)</xsl:text>
</xsl:template>

<xsl:template match="Cons">
	<xsl:apply-templates select="Name" />
	<xsl:apply-templates select="Arrow" />
	<xsl:apply-templates select="List" />
</xsl:template>

<xsl:template match="Arrow">
	<xsl:text> -&gt; </xsl:text>
</xsl:template>

<xsl:template match="List">
	<xsl:text>[]</xsl:text>
</xsl:template>

<xsl:template match="Var">
	<xsl:apply-templates select="Name" />
</xsl:template>

<xsl:template match="Locals">
   <xsl:for-each select="Function|PatDecl">
      <xsl:if test="(position() = 1)">
         <xsl:apply-templates select="." >
           <xsl:with-param name = "NoBr" >true</xsl:with-param>
         </xsl:apply-templates>
      </xsl:if>
      <xsl:if test="not(position() = 1)">
         <xsl:apply-templates select="." >
           <xsl:with-param name = "NoBr" >true</xsl:with-param>
         </xsl:apply-templates>
      </xsl:if>      
  </xsl:for-each>
</xsl:template>

<xsl:template match="Let">
    <xsl:param name = "Second" />
    <xsl:param name = "Pos" />
    <xsl:if test="($Second=&quot;true&quot;) or ($Pos=&quot;Left&quot;)">
      <xsl:text>(</xsl:text>
    </xsl:if>
    <xsl:text>let { &#10;</xsl:text>
    <xsl:apply-templates select="Locals" />
    <xsl:text>} in </xsl:text>
    <xsl:apply-templates select="Term" />
    <xsl:if test="($Second=&quot;true&quot;) or ($Pos=&quot;Left&quot;)">
      <xsl:text>)</xsl:text>
    </xsl:if>
</xsl:template>

<xsl:template match="Where">
   <xsl:apply-templates select="Term" />
   <xsl:text> where { &#10;</xsl:text>
   <xsl:apply-templates select="Locals"/>
   <xsl:text> }</xsl:text>
</xsl:template>

<xsl:template match="Where" mode="noexp" >
    <xsl:text> where { &#10;</xsl:text>
    <xsl:apply-templates select="Locals"/>
   <xsl:text> }</xsl:text>
</xsl:template>

<xsl:template match="If">
    <xsl:param name = "Second" />
    <xsl:param name = "Pos" />
    <xsl:if test="($Second=&quot;true&quot;) or ($Pos=&quot;Left&quot;)">
      <xsl:text>(</xsl:text>
    </xsl:if>
   <xsl:text> if </xsl:text>
   <xsl:apply-templates select="Term[1]" />
   <xsl:text> then </xsl:text>
   <xsl:apply-templates select="Term[2]" />
   <xsl:text> else </xsl:text>
   <xsl:apply-templates select="Term[3]" />
    <xsl:if test="($Second=&quot;true&quot;) or ($Pos=&quot;Left&quot;)">
      <xsl:text>)</xsl:text>
    </xsl:if>
</xsl:template>

<xsl:template match="TypeSchema">
   <xsl:apply-templates select="Constraints" />
   <xsl:apply-templates select="Term" />
</xsl:template>

<xsl:template match="DataType">
   <xsl:text>data </xsl:text>
   <xsl:apply-templates select="TypeSchema" />
   <xsl:text> = </xsl:text>
   <xsl:for-each select="Constr" >
        <xsl:apply-templates select="." />
		<xsl:if test="not(position() = last())">
			<xsl:text> | </xsl:text>
		</xsl:if>
  </xsl:for-each>
  <xsl:apply-templates select="Derivings" />
 <xsl:text>;&#10;</xsl:text>
  <xsl:apply-templates select="InfixDecl" />
 <xsl:text>&#10;</xsl:text>
</xsl:template>

<xsl:template match="NewType">
   <xsl:text>newtype </xsl:text>
   <xsl:apply-templates select="TypeSchema" />
   <xsl:text> = </xsl:text>
   <xsl:for-each select="Constr" >
        <xsl:apply-templates select="." />
		<xsl:if test="not(position() = last())">
			<xsl:text> | </xsl:text>
		</xsl:if>
  </xsl:for-each>
  <xsl:apply-templates select="Derivings" />
 <xsl:text>;&#10;</xsl:text>
  <xsl:apply-templates select="InfixDecl" />
 <xsl:text>&#10;</xsl:text>
</xsl:template>

<xsl:template match="Tuple">
   <xsl:text>(</xsl:text>
   <xsl:for-each select="Term" >
        <xsl:apply-templates select="." />
		<xsl:if test="not(position() = last())">
			<xsl:text>,</xsl:text>
		</xsl:if>
   </xsl:for-each>
   <xsl:text>)</xsl:text>
</xsl:template>

<xsl:template match="Class">
   <xsl:text>class </xsl:text>
   <xsl:apply-templates select="Constraints" />
   <xsl:apply-templates select="Constraint" />
   <xsl:text> where {</xsl:text>
  <xsl:text>&#10;</xsl:text>
   <xsl:apply-templates select="Members" />
  <xsl:text>}&#10;</xsl:text>
</xsl:template>

<xsl:template match="Instance">
   <xsl:text>instance </xsl:text>
   <xsl:apply-templates select="Constraints" />
   <xsl:apply-templates select="Constraint" />
   <xsl:text> where { </xsl:text>
  <xsl:text>&#10;</xsl:text>
   <xsl:apply-templates select="Members" />
  <xsl:text>}&#10;</xsl:text>
</xsl:template>

<xsl:template match="Constr[@infix=&quot;false&quot;]">
   <xsl:apply-templates select="Name" />
   <xsl:text> </xsl:text>
   <xsl:for-each select="Type">
		<xsl:apply-templates select="Term">
           <xsl:with-param name = "Second" >true</xsl:with-param>
        </xsl:apply-templates>
        <xsl:text> </xsl:text>
  </xsl:for-each>
</xsl:template>

<xsl:template match="Constr[@infix=&quot;true&quot;]">
   <xsl:apply-templates select="Type[1]" />
   <xsl:text> </xsl:text>
   <xsl:apply-templates select="Name" />
   <xsl:text> </xsl:text>
   <xsl:apply-templates select="Type[2]" />
</xsl:template>

<xsl:template match="Type">
   <xsl:param name = "Second" />
   <xsl:apply-templates select="Term">
      <xsl:with-param name = "Second" ><xsl:value-of select="$Second"/></xsl:with-param>
   </xsl:apply-templates>
</xsl:template>

<xsl:template match="PatDecl">
   <xsl:param name = "NoBr" />
   <xsl:apply-templates select="Pattern" />
   <xsl:text> = </xsl:text>
   <xsl:apply-templates select="Term" />
   <xsl:if test="not($NoBr=&quot;true&quot;)">
    <xsl:text>&#10;</xsl:text>
    <xsl:text>&#10;</xsl:text>
   </xsl:if>
</xsl:template>

<xsl:template match="InfixDecl[@infix=&quot;Left&quot;]">
   <xsl:text>infixl </xsl:text>
   <xsl:value-of select="@priority" />
   <xsl:text> </xsl:text>
   <xsl:apply-templates select="Name" />
  <xsl:text>;&#10;</xsl:text>
</xsl:template>

<xsl:template match="InfixDecl[@infix=&quot;Non&quot;]">
   <xsl:text>infix </xsl:text>
   <xsl:value-of select="@priority" />
   <xsl:text> </xsl:text>
   <xsl:apply-templates select="Name" />
  <xsl:text>;&#10;</xsl:text>
</xsl:template>

<xsl:template match="InfixDecl[@infix=&quot;Right&quot;]">
   <xsl:text>infixr </xsl:text>
   <xsl:value-of select="@priority" />
   <xsl:text> </xsl:text>
   <xsl:apply-templates select="Name" />
  <xsl:text>;&#10;</xsl:text>
</xsl:template>

<xsl:template match="Function">
    <xsl:param name = "NoBr" />
	<xsl:if test="count(TypeSchema) > 0">
        <xsl:apply-templates select="Name" />
        <xsl:text> :: </xsl:text>
    	<xsl:apply-templates select="TypeSchema" />
       <xsl:text>;&#10;</xsl:text>
	</xsl:if>
    <table cellspacing="0" cellpadding="0" border="0" frame="void" >
    <xsl:for-each select="Rule">
        <xsl:apply-templates select=".">
           <xsl:with-param name = "Name" >
              <xsl:apply-templates select="../Name" />
          </xsl:with-param>
        </xsl:apply-templates>
    </xsl:for-each>
    </table>
    <xsl:if test="not($NoBr=&quot;true&quot;)">
      <xsl:text>&#10;</xsl:text>
    </xsl:if>
</xsl:template>

<xsl:template match="Rule">
   <xsl:param name = "NoBr" />
   <xsl:param name = "Name" />
   <xsl:value-of select="$Name" />
   <xsl:text> </xsl:text>
   <xsl:apply-templates select="Pattern" />
   <xsl:if test="(count(Conditions) = 0) and (count(Term/Where/Conditions) = 0)">
       <xsl:text>= </xsl:text>
       <xsl:apply-templates select="Term"/>
   </xsl:if>
   <xsl:if test="(count(Conditions) = 1) ">
     <table cellspacing="0" cellpadding="0" border="0" frame="void" >
     <xsl:apply-templates select="Conditions">
        <xsl:with-param name = "Arrow" ><xsl:text>=</xsl:text></xsl:with-param>
     </xsl:apply-templates>
     </table>
   </xsl:if>
  <xsl:if test="(count(Term/Where/Conditions) = 1)">
     <table cellspacing="0" cellpadding="0" border="0" frame="void" >
     <xsl:apply-templates select="Term/Where/Conditions">
        <xsl:with-param name = "Arrow" ><xsl:text>=</xsl:text></xsl:with-param>
     </xsl:apply-templates>
     </table>
   </xsl:if>
   <xsl:text>;&#10;</xsl:text>
</xsl:template>

<xsl:template match="Pattern">
   <xsl:for-each select="Term">
		<xsl:apply-templates select=".">
          <xsl:with-param name = "Second" >true</xsl:with-param>
        </xsl:apply-templates>
        <xsl:text> </xsl:text>
  </xsl:for-each>
</xsl:template>

<xsl:template match="Members">
   <xsl:if test="count(Function|InfixDecl) > 0">
   <xsl:apply-templates select="Function|InfixDecl" >
          <xsl:with-param name = "NoBr" >true</xsl:with-param>
   </xsl:apply-templates>
   </xsl:if>
</xsl:template>

<xsl:template match="Constraint">
   <xsl:apply-templates select="ClassName" />
   <xsl:text> </xsl:text>
   <xsl:apply-templates select="Term" />
</xsl:template>

<xsl:template match="Constraints">
   <xsl:if test="count(Constraint) > 0">
     <xsl:if test="count(Constraint) > 1">
	 	<xsl:text>(</xsl:text>
     </xsl:if>
     <xsl:for-each select="Constraint">
		<xsl:apply-templates select="." />
		<xsl:if test="not(position() = last())">
			<xsl:text>, </xsl:text>
		</xsl:if>
     </xsl:for-each>
      <xsl:if test="count(Constraint) > 1">
		<xsl:text>)</xsl:text>
      </xsl:if>
      <xsl:text> =&gt; </xsl:text>
    </xsl:if>
</xsl:template>

<xsl:template match="Derivings">
   <xsl:if test="count(Name) > 0">
     <xsl:text> deriving </xsl:text>
     <xsl:if test="count(Name) > 1">
	 	<xsl:text>(</xsl:text>
     </xsl:if>
     <xsl:for-each select="Name">
		<xsl:apply-templates select="." />
		<xsl:if test="not(position() = last())">
			<xsl:text>, </xsl:text>
		</xsl:if>
     </xsl:for-each>
      <xsl:if test="count(Name) > 1">
		<xsl:text>)</xsl:text>
      </xsl:if>
    </xsl:if>
</xsl:template>

<xsl:template match="MainModule">
        <xsl:text>mainModule </xsl:text>
	<xsl:apply-templates select="Name" />
      <xsl:text> &#10;</xsl:text>
</xsl:template>

<xsl:template match="Qualified">
        <xsl:text>qualified </xsl:text>
</xsl:template>

<xsl:template match="Import">
        <xsl:text>import </xsl:text>
	<xsl:apply-templates select="Qualified" />
	<xsl:apply-templates select="Name" />
        <xsl:text>;&#10;</xsl:text>
</xsl:template>

<xsl:template match="Default">
        <xsl:text>default(</xsl:text>      
        <xsl:for-each select="Name">
	   <xsl:apply-templates select="." />
	   <xsl:if test="not(position() = last())">
	      <xsl:text>,</xsl:text>
           </xsl:if>
        </xsl:for-each>
        <xsl:text>);&#10;</xsl:text>	
</xsl:template>

<xsl:template match="Module">
      <xsl:text>module </xsl:text>
	<xsl:apply-templates select="Name" />
      <xsl:text> where {&#10;</xsl:text>      
      <xsl:for-each select="Imports|Default|DataTypes|Classes|Instances|Function|PatDecl|InfixDecl">
           <xsl:apply-templates select="." />
      </xsl:for-each>
      <xsl:text>}&#10;</xsl:text>
</xsl:template>

<xsl:template match="Name">
	<xsl:apply-templates select="text()" />
</xsl:template>

<xsl:template match="text()">
	<xsl:value-of select="normalize-space()" />
</xsl:template>

</xsl:stylesheet>
