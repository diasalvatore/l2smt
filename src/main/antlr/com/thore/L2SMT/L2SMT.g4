grammar L2SMT;

@header {
    package com.thore.L2SMT;

    import java.util.*;
    import org.apache.commons.lang3.math.*;
}

@members {
    private enum Type { Bool, Int, Real, String, AttrDS, AttrE, Role, DS }
    private String currentLabel;
    private int currentLabelCounter = 0;
    private Set<String> atoms = new HashSet<>();
    private Map<String, Type> tempType = new HashMap<>();
    private Map<String, List<List<String>>> owning = new HashMap<>();
    private Map<String, String> stringPool = new TreeMap<>();
    private List<String> smt_expr = new LinkedList<>();
    private List<String> smt_typeparam = new LinkedList<>();
    private Type[] mutual_exclusive =  { Type.Bool, Type.Int, Type.Real, Type.String, Type.Role, Type.DS };
    private StringBuilder __output = new StringBuilder();


    /**
    * Returns translated SMT
    */  
    public String getSMT() {
        return __output.toString();
    }


    /**
    * Returns current label
    */    
    private String getCurrentLabel() {
        return currentLabel;
    }


    /**
    * Set current label
    */    
    private void setCurrentLabel(String label) {
        currentLabel = label.substring(1,label.length()-1).replace(" ", "");
        currentLabelCounter = 0;
    }


    /**
    * Returns true if two type are incompatible
    */
    private boolean areMutualExclusive(Type t1, Type t2) {
        return ( (Arrays.asList(mutual_exclusive).contains(t1) && Arrays.asList(mutual_exclusive).contains(t2)) );
    }


    /**
    * Adds fe
    */
    private void updateOwner(String name, List<String> nple) {
        if (!owning.containsKey(name)) owning.put(name, new LinkedList<List<String>>());      
        
        List<List<String>> o = owning.get(name);

        if (nple != null) o.add(nple);
    }


    /**
    * Adds Atom name and its type to pools
    */
    private void updateAtom(String name, Type type) {
        atoms.add(name);

        if (type != null) {
            updateOwner("is"+type.toString(), Arrays.asList(new String[] { name }));
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
    * GetType of AttrE, AttrDS, Var
    */
    private Type getType(String pool, String name) {
        return Type.Bool; // ToDo
    }


    /**
    * Check that type of t1 is the same of t2, otherwise exit with error!
    */
    private Type cType(Type t1, Type t2, String error) {
        if (t1 != t2) {
            System.err.println("["+currentLabel+"]\nERROR: " + error);
            System.exit(-1);
        } 

        return t1;
    }


    /**
    * Add expression to evaluation set
    */
    private void addExpr(String expr) {
        smt_expr.add((currentLabelCounter == 0 ? "\n; ["+currentLabel+"]\n":"")+"(assert (! "+expr+" :named "+currentLabel+"_"+(currentLabelCounter++)+"))");
    }


    /**
    * Service method used by printSMT for 
    */
    private void out(String s) {
        __output.append(s);
    }


    /**
    * Generate SMT using out
    */
    private void printSMT() {
        String tmp;
        int i;

        // Declaring all is* function type
        for (Type t : Type.values()) updateOwner("is"+t, null);
        

        // OPTIONS
        out("(set-option :produce-unsat-cores true)\n\n");
        
        // PREAMBLE
        out("; sort\n(define-sort Atom () Int)\n\n");


        // System.out.println(reorderedAtoms);

 //       out()    "\n; predicates\n"+
 //           "(declare-fun hasAttr (Atom Atom) Bool)\n"+
 //           "(declare-fun hasRole (Atom Atom) Bool)\n"+
 //           "(declare-fun provides (Atom Atom) Bool)\n"+
 //           "(declare-fun consumes (Atom Atom) Bool)\n"+
 //           "(declare-fun uses (Atom Atom) Bool)\n"+
 //           "(declare-fun valueOf (Atom) Int)\n"+
 //           "(declare-fun nameOf (Atom) Int)\n");
//
 //       for (Type t : Type.values()) {
 //           out("(declare-fun is"+t+" (Atom) Bool)\n");
 //       }      

        out("\n; atoms\n");
        
        // atoms 
        String nameOfs = "";
        for (String atom : atoms) {
            out("(declare-const "+atom+" Atom)\n");

            // nameOfs
            int lio = atom.lastIndexOf('.');
            String tmp_name = (lio != -1 ? atom.substring(lio+1) : atom);
            nameOfs += "(assert (= (nameOf "+atom+") "+addStringPool(tmp_name)+"))\n";
        }

        // strings
        for (Map.Entry<String, String> entry : stringPool.entrySet()) {
            out("(declare-const "+entry.getValue()+" Atom) ; "+entry.getKey()+"\n");        
        }



        // predicates
        out("\n; predicates\n");
        out(
            "(declare-fun valueOf (Atom) Int)\n"+
            "(declare-fun nameOf (Atom) Int)\n");

        // Map<Type, List<String>> reorderedAtoms = new HashMap<>();
        // for (Type t : mutual_exclusive) reorderedAtoms.put(t, new LinkedList<String>());
        // for (Map.Entry<String, Type> atom : atoms.entrySet()) reorderedAtoms.get(atom.getValue()).add(atom.getKey());

        // for (Map.Entry<Type, List<String>> atom : reorderedAtoms.entrySet()) {
        //     tmp = "(define-fun is"+atom.getKey()+" ((a Atom)) Bool";

        //     if (atom.getValue().size() > 0) {
        //         tmp += " (if (or";
        //         for (String a : atom.getValue()) tmp += " (= a "+a+")";
        //         tmp += ") true false)"; 
        //     } else {
        //         tmp += " false";
        //     }

        //     out(tmp+")\n");
        // }


        for (Map.Entry<String, List<List<String>>> f : owning.entrySet()) {
            int max = 1;
            tmp = "";

            if (f.getValue().size() > 0) {
                tmp += " (if (or";
    
                for (List<String> nple : f.getValue()) {
                    if (nple.size() > max) max = nple.size();
                    i = 0;

                    if (nple.size() > 1) tmp += " (and";
                    for (String val : nple) {
                        tmp += " (= p"+(i++)+" "+val+")";
                    }
                    if (nple.size() > 1) tmp += ")";
                }
                tmp += ") true false)"; 
            } else {
                tmp += " false";
            }

            String tmp2 = "(define-fun "+f.getKey()+" (";
            for (i=0;i<max;i++) tmp2 += "(p"+i+" Atom) ";
            tmp2 += ") Bool "+"\n    "+tmp;

            out(tmp2+"\n)\n");
        }




        // atoms unique val
        out("\n; atoms unique val \n");
        i = 0;
        for (String atom : atoms) {
            out("(assert (= "+atom+" "+i+"))\n");
            i++;
        }

        // strings unique val
        for (Map.Entry<String, String> entry : stringPool.entrySet()) {
            out("(assert (! (and (= "+entry.getValue()+" "+i+") (= (valueOf "+entry.getValue()+") "+i+") ) :named _StringPool_"+i+"))\n");
            i++;
        }
        
        // namesOf
        out("\n; atoms names\n"+nameOfs);

        out("\n; parameters\n");
        i = 0;
        for (String expr : smt_typeparam) 
            out("(assert (! "+expr+"  :named _P"+(i++)+"))\n");



        // uninterpreted functions properties

        // every atom has a type
        out("\n; ---== Properties ==---\n");
        tmp = "";
        // for (Type t : mutual_exclusive) tmp += " (= (is"+t+" x) true)";
        // out("\n; every atom has a type\n(assert (forall ((x Atom)) (or"+tmp+")))\n");


        // the following predicates are mutually exclusive
        tmp = "";
        out("\n; the following predicates are mutually exclusive\n");
        for (Type t : mutual_exclusive) {
            tmp += "(assert (! (forall ((x Atom)) (=> (= (is"+t+" x) true) (and";
            for (Type t2 : mutual_exclusive) if (t2 != t) tmp += " (= (is"+t2+" x) false)";
            tmp += "))) :named multipleType_"+t+"))\n";
        }
        out(tmp);



        // AttrDS haven't multiple owners
        //out("\n; AttrDS haven't multiple owners\n"+
        //    "(assert (! (forall ((x Atom) (y Atom)) (=> (and (= (isDS x) true) (= (hasAttr x y) true)) (forall ((z Atom)) (=> (and (= (isDS z) true) (not (= x z))) (not (= (hasAttr z y) true)) )))) :named _UniqueHasAttr)) \n");

        out("\n\n; ---=== User Defined Assertions ===--- ");
        for (String expr : smt_expr) {
            out(expr+"\n");
        }

        out("\n\n(check-sat)\n");
        out("(get-unsat-core)\n");
        // System.out.println("(get-model)");
        // System.out.println(owning);
    }


    /**
    * Add a type assertion for the Quantified Variable (it will be asserted to be an Atom, but after domain will be restricted by getQuantifierTypes)
    */
    private String addQuantifierType(String var, Type t) {
        if (t == Type.AttrDS || t == Type.AttrE || t == Type.DS || t == Type.Role) {
            tempType.put(var, t);

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


    /**
    * Adds a string to the pool and returns an uid
    */
    private String addStringPool(String s) {
        s = s.replace("\"","");
        if (!stringPool.containsKey(s)) {
            stringPool.put(s, "string"+stringPool.size());
        } 

        return stringPool.get(s);
    }


    /**
    * Translate values using valueOf or not
    */
    private String valueOfOrNot(String s) {
        if (NumberUtils.isNumber(s)) { // ToDo: consider other cases than numbers
            return s;
        } else {
            return " (valueOf " + s + " ) ";
        }
    }
}










// ------------------------------- GRAMMAR -------------------------------






program returns [String s]:    
            (l=LABEL { setCurrentLabel($l.text); } (p=pred { addExpr($p.s); } EOP)+)+ { printSMT(); };

pred returns [String s, Type t]:
            op=('FORALL'|'EXISTS')                                   { $s = "("+($op.text.equals("FORALL") ? "forall" : "exists")+" ("; }
            v=ID ':' ty=TYPE                                         { $s += addQuantifierType($v.text, Type.valueOf($ty.text)); }
            (',' v=ID ':' ty=TYPE                                    { $s += addQuantifierType($v.text, Type.valueOf($ty.text)); })* 
            '{' p=pred '}'                                           {
                                                                       $t = cType($p.t, Type.Bool, $op.text + " predicate should be Bool"); 
                                                                       $s += ") (=> "+getQuantifierTypes()+" "+$p.s+"))"; 
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
                                                                       $s = "("+transOp($op.text)+valueOfOrNot($p1.s)+ " " +valueOfOrNot($p2.s)+")"; 
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
                      $s = addStringPool($BOOL.text); 

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
                      $s = addStringPool($STRING.text); 
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
    |       VAR     { 
                      $t = getType("VAR", $VAR.text);
                      $s = $VAR.text; 
                      updateAtom($VAR.text, null);
                    }    
    |       ID     { 
                      $t = null;
                      $s = $ID.text; 
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
                                                    updateOwner("isAttrE", Arrays.asList(new String[] { $t1.text })); 
                                                  }
    |       'IsAttrDS(' t1=term ')'               { 
                                                    $t = Type.Bool;
                                                    $s = "(= (isAttrDS "+$t1.s+") true)";
                                                    //updateAtom($t1.text, Type.AttrDS); 
                                                    updateOwner("isAttrDS", Arrays.asList(new String[] { $t1.text })); 
                                                  }   
    |       'NameOf(' t1=term ',' str=STRING ')'  { 
                                                    $t = Type.Bool;
                                                    $s = "(= (nameOf "+$t1.text+") "+addStringPool($str.text)+")";
                                                  }
    |       'HasAttr(' t1=term ',' t2=term ')'    { 
                                                    $t = Type.Bool;
                                                    $s = "(= (hasAttr "+$t1.text+" "+$t2.text+") true)";
                                                    updateAtom($t1.text, Type.DS); 
                                                    updateAtom($t2.text, Type.AttrDS);  //Arrays.asList(new String[]{"one", "two", "three"});
                                                    updateOwner("hasAttr", Arrays.asList(new String[] { $t1.text, $t2.text })); 
                                                  }
    |       'HasRole(' t1=term ',' t2=term ')'       { 
                                                    $t = Type.Bool;
                                                    $s = "(= (hasRole "+$t1.text+" "+$t2.text+") true)";
                                                    updateAtom($t1.text, Type.DS); 
                                                    updateAtom($t2.text, Type.Role); 
                                                    updateOwner("hasRole", Arrays.asList(new String[] { $t1.text, $t2.text })); 
                                                  }
    |       'Provides(' t1=term ',' t2=term  ')'     { 
                                                    $t = Type.Bool;
                                                    $s = "(= (provides "+$t1.text+" "+$t2.text+") true)";
                                                    updateAtom($t1.text, Type.DS); 
                                                    updateAtom($t2.text, Type.Role); 
                                                    updateOwner("provides", Arrays.asList(new String[] { $t1.text, $t2.text })); 
                                                  }
    |       'Consumes(' t1=term ',' t2=term  ')'     { 
                                                    $t = Type.Bool;
                                                    $s = "(= (consumes "+$t1.text+" "+$t2.text+") true)";
                                                    updateAtom($t1.text, Type.DS); 
                                                    updateAtom($t2.text, Type.Role); 
                                                    updateOwner("consumes", Arrays.asList(new String[] { $t1.text, $t2.text })); 
                                                  }
    |       'Bond(' t1=term ',' t2=term  ',' t3=term ')' { 
                                                    $t = Type.Bool;
                                                    $s = "(= (bond "+$t1.text+" "+$t2.text+" "+$t3.text+") true)";
                                                    updateAtom($t1.text, Type.DS); 
                                                    updateAtom($t2.text, Type.DS); 
                                                    updateAtom($t3.text, Type.Role); 
                                                    updateOwner("bond", Arrays.asList(new String[] { $t1.text, $t2.text, $t3.text })); 
                                                    updateOwner("uses", Arrays.asList(new String[] { $t1.text, $t2.text })); 
                                                  }
    |       'Uses(' t1=term ',' t2=term  ')'           { 
                                                    $t = Type.Bool;
                                                    $s = "(= (uses "+$t1.text+" "+$t2.text+") true)";
                                                    updateAtom($t1.text, Type.DS); 
                                                    updateAtom($t2.text, Type.DS); 
                                                  }
    ; 
           
           

           
           
           
// *** LEXER ***
TYPE:       'Bool' | 'Int' | 'Real' | 'String' | 'AttrE' | 'AttrDS' | 'Role' | 'DS'; 

// operators
AND:        '&&' | 'and';
OR:         '||' | 'or';
NOT:        '!'  | 'not';
IMPLIES:    '=>' | 'implies';

// litterals
BOOL:       'True' | 'False'| 'true' | 'false';
INT:        '-'? DIGIT+;
REAL:       INT+ '.' INT+;
STRING:     ('\'' ALLCHAR* '\'')|('"' ALLCHAR* '"');
ATTRE:      'AE.' ID;
ATTRDS:     'AD.' ID '.' ID;
ROLE:       'R.' ID;
DS:         'DS.' ID;
VAR:        '$' ID;
LABEL:      '[' ALLCHAR+ ']';


ID:         [a-z] [a-zA-Z0-9]*;


fragment 
ALLCHAR:    [a-zA-Z0-9 ];       

DIGIT:      [0-9]+ ;             
WS:         [ \n\r\t]+ -> skip ; // skip spaces, tabs, newlines, \r (Windows)
COMMENT:    ('#'|'//') ~( '\r' | '\n' )* -> skip;
EOP:        [;]+;