grammar L2SMT;

@header {
    package com.thore.L2SMT;

    import com.thore.language.*;
    import java.util.*;
    import java.util.regex.*;
    import org.apache.commons.lang3.math.*;
}

@parser::members {
    private List<String> currentLabel;
    private String currentLabelId;
    private int currentLabelCounter = 0;
    private Map<String, Type> tempType = new HashMap<>();
    private List<SystemState> sss = new ArrayList<>();
    private SystemState ss = new SystemState();

    public List<SystemState> getSystemStates() {
        return sss;
    }

    private void newState() {
        sss.add(ss); 
        ss = ss.clone();
    }

    private void addLabel(String label) {
        String l = label.substring(1,label.length()-1).replace(" ", "");
        currentLabel.add(l);
        if (currentLabelId.equals("") || l.startsWith("#")) currentLabelId = "id"+l.replace("#","").replaceAll("-","");
    }

    private void resetLabel() {
        currentLabel = new LinkedList<>();
        currentLabelCounter = 0;
        currentLabelId = "";
    }

    private Type getType(String pool, String name) {
        return Type.Bool; // ToDo
    }

    private Type cType(Type t1, Type t2, String error) {
        if (t1 != t2) {
            System.err.println("["+currentLabel+"]\nERROR: " + error);
            System.exit(-1);
        } 

        return t1;
    }

    private void addExpr(String expr) {
        if (expr != null && !expr.isEmpty())
            ss.addExpr((currentLabelCounter == 0 ? "\n; ["+currentLabel+"]\n":"")+"(assert (! "+expr+" :named "+currentLabelId+"_"+(currentLabelCounter++)+"))");
    }

    private String addQuantifierType(String var, Type t) {
        if (t == Type.AttrDS || t == Type.AttrE || t == Type.DS || t == Type.Role) {
            tempType.put(var, t);
            // System.out.println("var:"+var);
            // System.out.println(tempType.entrySet());
            return "("+var+" Atom) ";          
        } else {
            return "("+var+" "+t+") ";          
        }
    }


    /**
    * Return domain assertions about quantified variables
    */
    private String getQuantifierTypes() {
        String ret = "";

        if (tempType.size() > 1) ret = "(and ";
        for (Map.Entry<String, Type> entry : tempType.entrySet()) {
            ret += "(= (is"+entry.getValue() + " " + entry.getKey()+") true) ";
        }
        if (tempType.size() > 1) ret += ")";

        tempType = new HashMap<>();

        return ret;
    }

    private void updateFunction(String name, List<String> nple) {
        for (String s : nple) {
            if (tempType.containsKey(s)) { // excluding quantified variables
                return;
            }
        }

        ss.updateFunction(name, nple);
    }    

    private void updateAtom(String name, Type type) {
        if (!tempType.containsKey(name)) { // excluding quantified variables
            ss.updateAtom(name, type);
        }
    }

    /**
    *   Translates L operators in SMT operators
    */
    private String transOp(String op) {
        String trans = op;
        switch (op) {
            case "&&":     trans = "and"; break;     
            case "||":     trans = "or";  break;   
            case "!":      trans = "not"; break;    
            case "==":     trans = "=";   break;  
        }

        return trans;
    }

    /**
    * Translate values using valueOf or not
    */
    private String valueOfOrNot(String s) {
        if (NumberUtils.isNumber(s) || s.equals("true")  || s.equals("false") ) { // ToDo: consider other cases than numbers
            return s;
        } else {
            return " (valueOf " + s + " ) ";
        }
    }

}










// ------------------------------- GRAMMAR -------------------------------






program returns [String s]:    
            { ss = new SystemState(); }
            (
                {resetLabel();}
                (STEP_DELIMITER { newState(); })?
                (l=LABEL { addLabel($l.text); })+
                ((p=pred { addExpr($p.s); })? EOP)+
            )+ 
            { newState(); }
    ;


pred returns [String s, Type t]:
            op=('FORALL'|'EXISTS')                                   { $s = "("+($op.text.equals("FORALL") ? "forall" : "exists")+" ("; }
            v=ID ':' ty=TYPE                                         { $s += addQuantifierType($v.text, Type.valueOf($ty.text)); }
            (',' v=ID ':' ty=TYPE                                    { $s += addQuantifierType($v.text, Type.valueOf($ty.text)); })* 
            '{' p=pred '}'                                           {
                                                                       // $t = cType($p.t, Type.Bool, $op.text + " predicate should be Bool"); 
                                                                       $t = Type.Bool; 
                                                                       if ($op.text.equals("FORALL")) {
                                                                          $s += ") (=> "+getQuantifierTypes()+" "+$p.s+"))"; 
                                                                       } else {
                                                                          $s += ") (and "+getQuantifierTypes()+" "+$p.s+"))"; 
                                                                       }
                                                                     }
    |       p1=pred op=(AND|OR) p2=pred                              {
                                                                       //cType($p1.t, Type.Bool, $op.text + " operands should be Bool");
                                                                       $t = cType($p2.t, Type.Bool, $op.text + " operands should be Bool");
                                                                       $s = "("+transOp($op.text)+" "+$p1.s+" "+$p2.s+")"; 
                                                                     }
    |       p1=pred op=('<'|'<='|'>='|'>'|'=='|'!=') p2=pred         {
                                                                       // todo 
                                                                       //cType($p1.t, Type.Int, $op.text + " operands should be Int");
                                                                       //$t = cType($p2.t, Type.Int, $op.text + " operands should be Int"); 
                                                                       $t = Type.Bool;
                                                                       // $s = "("+transOp($op.text)+" (valueOf "+$p1.s+") (valueOf "+$p2.s+"))"; 
                                                                       if ($op.text.equals("!=")) {
                                                                          $s = "(not (= "+valueOfOrNot($p1.s)+ " " +valueOfOrNot($p2.s)+"))"; 
                                                                       } else {
                                                                          $s = "("+transOp($op.text)+" "+valueOfOrNot($p1.s)+ " " +valueOfOrNot($p2.s)+")"; 
                                                                       }
                                                                     }
    |       p1=pred op=('+'|'-') p2=pred                             {
                                                                       // todo 
                                                                       cType($p1.t, Type.Int, $op.text + " operands should be Int");
                                                                       $t = cType($p2.t, Type.Int, $op.text + " operands should be Int"); 
                                                                       $s = "("+transOp($op.text)+valueOfOrNot($p1.s)+ " " +valueOfOrNot($p2.s)+")"; 
                                                                     }
    |       p1=pred op=('*'|'/') p2=pred                             {
                                                                       cType($p1.t, Type.Int, $op.text + " operands should be Int");
                                                                       $t = cType($p2.t, Type.Int, $op.text + " operands should be Int"); 
                                                                       $s = "("+transOp($op.text)+valueOfOrNot($p1.s)+ " " +valueOfOrNot($p2.s)+")"; 
                                                                       //$s = "("+$op.text+" (valueOf "+$p1.s+") (valueOf "+$p2.s+"))"; 
                                                                     }
    |       p1=pred IMPLIES p2=pred                                     {
                                                                       cType($p1.t, Type.Bool, "=> LHS should be Bool");
                                                                       $t = cType($p2.t, Type.Bool, "=> RHS should be Bool"); 
                                                                       $s = "(=> "+$p1.s+" "+$p2.s+")"; 
                                                                     }
    |       NOT p=pred                                               {
                                                                       $t = cType($p.t, Type.Bool, "! arg should be Bool"); 
                                                                       $s = "(not "+$p.s+")"; 
                                                                     }
    |       f=function                                               {
                                                                       $t = $f.t;  
                                                                       $s = $f.s; 
                                                                     }
    |       te=term                                                  {
                                                                       $t = $te.t; 
                                                                       $s = $te.s; 
                                                                     }
    |       '(' p=pred ')'                                           {
                                                                       $t = $p.t;  
                                                                       $s = $p.s; 
                                                                     }  
    ;
    
term returns [String s, Type t]:       
            BOOL    { 
                      $t = Type.Bool;
                      // $s = $BOOL.text; 
                      $s = ss.addStringPool($BOOL.text); 

                    }
    |       INT     { 
                      $t = Type.Int;
                      $s = $INT.text; 
                    }
    |       REAL    { 
                      $t = Type.Real;
                      $s = $REAL.text; 
                    }
    |       STRING  { 
                      $t = Type.String;
                      $s = ss.addStringPool($STRING.text); 
                    }
    |       ATTRE   { 
                      $t = getType("AttrE", $ATTRE.text);
                      $s = $ATTRE.text; 
                      updateAtom($ATTRE.text, null);
                    }
    |       ATTRDS  { 
                      $t = getType("AttrDS", $ATTRDS.text);
                      $s = $ATTRDS.text; 
                      updateAtom($ATTRDS.text, null);
                    }
    |       ROLE    { 
                      $t = Type.Role;
                      $s = $ROLE.text; 
                      updateAtom($ROLE.text, null);
                    }
    |       DS      { 
                      $t = Type.DS;
                      $s = $DS.text; 
                      updateAtom($DS.text, null);
                    }   
    |       ID      {  
                      $t = null;
                      $s = $ID.text; 
                      updateAtom($ID.text, null);
                    }
    |       '^'ID   { 
                      $t = null;
                      $s = "["+$ID.text+"]"; 
                      updateAtom($ID.text, null);
                    }
    ;

function returns [String s, Type t]:  
            'IsBool(' t1=term ')'                 { 
                                                    $t = Type.Bool;
                                                    $s = "(= (isBool "+$t1.s+") true)";
                                                    updateAtom($t1.s, Type.Bool);
                                                  }
    |       'IsInt(' t1=term ')'                  { 
                                                    $t = Type.Bool;
                                                    $s = "(= (isInt "+$t1.s+") true)";
                                                    updateAtom($t1.s, Type.Int);
                                                  }
    |       'IsReal(' t1=term ')'                 { 
                                                    $t = Type.Bool;
                                                    $s = "(= (isReal "+$t1.s+") true)";
                                                    updateAtom($t1.s, Type.Real);
                                                  }
    |       'IsString(' t1=term ')'               { 
                                                    $t = Type.Bool;
                                                    $s = "(= (isString "+$t1.s+") true)";
                                                    updateAtom($t1.s, Type.String);
                                                  }
    |       'IsRole(' t1=term ')'                 { 
                                                    $t = Type.Bool;
                                                    $s = "(= (isRole "+$t1.s+") true)";
                                                    updateAtom($t1.s, Type.Role);
                                                  }
    |       'IsDS(' t1=term ')'                   { 
                                                    $t = Type.Bool;
                                                    $s = "(= (isDS "+$t1.s+") true)";
                                                    updateAtom($t1.s, Type.DS);
                                                  }
    |       'IsAttrE(' t1=term ')'                { 
                                                    $t = Type.Bool;
                                                    $s = "(= (isAttrE "+$t1.s+") true)";
                                                    //updateAtom($t1.text, Type.AttrE); 
                                                    updateFunction("isAttrE", Arrays.asList(new String[] { $t1.text })); 
                                                  }
    |       'IsAttrDS(' t1=term ')'               { 
                                                    $t = Type.Bool;
                                                    $s = "(= (isAttrDS "+$t1.s+") true)";
                                                    //updateAtom($t1.text, Type.AttrDS); 
                                                    updateFunction("isAttrDS", Arrays.asList(new String[] { $t1.text })); 
                                                  }   
    |       'NameOf(' t1=term ',' str=STRING ')'  { 
                                                    $t = Type.Bool;
                                                    $s = "(= (nameOf "+$t1.text+") "+ss.addStringPool($str.text)+")";
                                                  }
    |       'HasAttr(' t1=term ',' t2=term ')'    { 
                                                    $t = Type.Bool;
                                                    $s = "(= (hasAttr "+$t1.text+" "+$t2.text+") true)";
                                                    updateAtom($t1.text, Type.DS); 
                                                    updateAtom($t2.text, Type.AttrDS);  //Arrays.asList(new String[]{"one", "two", "three"});
                                                    updateFunction("hasAttr", Arrays.asList(new String[] { $t1.text, $t2.text })); 
                                                  }
    |       'HasRole(' t1=term ',' t2=term ')'       { 
                                                    $t = Type.Bool;
                                                    $s = "(= (hasRole "+$t1.text+" "+$t2.text+") true)";
                                                    updateAtom($t1.text, Type.DS); 
                                                    updateAtom($t2.text, Type.Role); 
                                                    updateFunction("hasRole", Arrays.asList(new String[] { $t1.text, $t2.text })); 
                                                  }
    |       'Provides(' t1=term ',' t2=term  ')'     { 
                                                    $t = Type.Bool;
                                                    $s = "(= (provides "+$t1.text+" "+$t2.text+") true)";
                                                    updateAtom($t1.text, Type.DS); 
                                                    updateAtom($t2.text, Type.Role); 
                                                    updateFunction("provides", Arrays.asList(new String[] { $t1.text, $t2.text })); 
                                                  }
    |       'Consumes(' t1=term ',' t2=term  ')'     { 
                                                    $t = Type.Bool;
                                                    $s = "(= (consumes "+$t1.text+" "+$t2.text+") true)";
                                                    updateAtom($t1.text, Type.DS); 
                                                    updateAtom($t2.text, Type.Role); 
                                                    updateFunction("consumes", Arrays.asList(new String[] { $t1.text, $t2.text })); 
                                                  }
    |       'Bond(' t1=term ',' t2=term  ',' t3=term ')' { 
                                                    $t = Type.Bool;
                                                    //$s = "(= (bond "+$t1.text+" "+$t2.text+" "+$t3.text+") true)";
                                                    $s = "(and (= (pre "+$t1.text+" "+$t2.text+" "+$t3.text+") true) (= (pre "+$t2.text+" "+$t1.text+" "+$t3.text+") true))";
                                                    updateAtom($t1.text, Type.DS); 
                                                    updateAtom($t2.text, Type.DS); 
                                                    updateAtom($t3.text, Type.Role); 
                                                    updateFunction("bond", Arrays.asList(new String[] { $t1.text, $t2.text, $t3.text })); 
                                                    updateFunction("uses", Arrays.asList(new String[] { $t1.text, $t2.text })); 
                                                  }
    |       'Uses(' t1=term ',' t2=term  ')'      { 
                                                    $t = Type.Bool;
                                                    $s = "(= (uses "+$t1.text+" "+$t2.text+") true)";
                                                    updateAtom($t1.text, Type.DS); 
                                                    updateAtom($t2.text, Type.DS); 
                                                    // updateFunction("uses", Arrays.asList(new String[] { $t1.text, $t2.text })); 
                                                  }
    |       'Precondition(' t1=term ','  r1=term ',' p1=pred  ')' { 
                                                    $t = Type.Bool;
                                                    if (tempType.size() > 0) {
                                                        $s = "(pre "+$t1.text+" "+$r1.text+" "+$p1.s+")";
                                                    } else {
                                                        $s = "";
                                                        ss.updateCondition("pre", $t1.text, $r1.text, $p1.s);
                                                    }
                                                  }
     |      'Postcondition(' t1=term ','  r1=term ',' p1=pred  ')' { 
                                                    $t = Type.Bool;
                                                    $s = "";
                                                    ss.updateCondition("post", $t1.text, $r1.text, $p1.s);
                                                  }
    ; 
           
           

           
           
           
// *** LEXER ***
TYPE:       'Bool' | 'Int' | 'Real' | 'String' | 'AttrE' | 'AttrDS' | 'Role' | 'DS'; 

// operators
AND:        '&&' | 'and';
OR:         '||' | 'or';
NOT:        '!'  | 'not';
IMPLIES:    '=>' | 'implies';
STEP_DELIMITER: '---STEP---';

// litterals
BOOL:       'True' | 'False'| 'true' | 'false';
INT:        '-'? DIGIT+;
REAL:       INT+ '.' INT+;
STRING:     ('\'' ALLCHAR* '\'')|('"' ALLCHAR* '"');
ATTRE:      'AE.' ID;
ATTRDS:     'AD.' ID '.' ID;
ROLE:       'R.' ID;
DS:         'DS.' ID;
LABEL:      '[' ('?'|'#')? ALLCHAR+ ']';


ID:         '$'?[a-z] [a-zA-Z0-9]*;


fragment 
ALLCHAR:    [a-zA-Z0-9\- ];       

DIGIT:      [0-9]+ ;             
WS:         [ \n\r\t]+ -> skip ; // skip spaces, tabs, newlines, \r (Windows)
COMMENT:    ('#'|'//') ~( '\r' | '\n' )* -> skip;
EOP:        [;]+;