grammar L2SMT;

@header {
    package com.thore.L2SMT;

    import java.util.*;
    import org.apache.commons.lang3.math.*;
    import java.util.regex.*;
}

@parser::members {
    private class Function {
        private String name;
        private int parameters;

        private Set<List<String>> tuples = new HashSet<>();

        public Function(String name, int parameters) {
            this.name = name;
            this.parameters = parameters;
        }

        public void addTuple(List<String> tuple) {
            if (tuple != null) {
                tuples.add(tuple);

                if (tuple.size() > parameters) parameters = tuple.size();
            }
        }

        public boolean equals(Object o) {
            if (o == null) return false;
            if (o.getClass() != this.getClass()) return false;
                
            Function f = (Function)o;
            return (f.name.toLowerCase().equals(this.name.toLowerCase()));
        }

        public String getSMT() {
            StringBuilder sb = new StringBuilder("");
            int i;

            if (tuples.size() == 0) {
                sb.append("false");
            } else {
                sb.append(" (if (or \n  ");
    
                for (List<String> t : tuples) {
                    if (t.size() > 1) sb.append(" (and");

                    i = 0;
                    for (String val : t) {
                        sb.append(" (= p"+(i++)+" "+val+")");
                    }

                    if (t.size() > 1) sb.append(")");
                    sb.append("\n  ");
                }
                sb.append(") true false)");
            }
            
            // return
            StringBuilder args = new StringBuilder();
            for (i=0;i<parameters;i++) args.append("(p"+i+" Atom) ");
            
            return "(define-fun "+name+" ("+args.toString()+") Bool "+sb+")\n";
        }
    }

    private enum Type { Bool, Int, Real, String, AttrDS, AttrE, Role, DS }
    private List<String> currentLabel;
    private String currentLabelId;
    private int currentLabelCounter = 0;
    private Set<String> atoms = new HashSet<>();
    private Map<String, Type> tempType = new HashMap<>();
    private Map<String, Function> functions = new HashMap<>();
    private Map<String, String> stringPool = new TreeMap<>();
    private List<String> smt_expr = new LinkedList<>();
    private List<String> smt_typeparam = new LinkedList<>();
    private Type[] mutual_exclusive =  { Type.Bool, Type.Int, Type.Real, Type.String, Type.Role, Type.DS };
    private StringBuilder __output = new StringBuilder();


    /**
    * Fake constructor
    */
    public void init() {
        // Declaring all is* function type
        for (Type t : Type.values()) functions.put("is"+t, new Function("is"+t, 1));

        // Declaring all functions
        functions.put("hasAttr", new Function("hasAttr", 2));
        functions.put("hasRole", new Function("hasRole", 2));
        functions.put("provides", new Function("provides", 2));
        functions.put("consumes", new Function("consumes", 2));
        functions.put("bond", new Function("bond", 2));
        functions.put("uses", new Function("uses", 2));
    }

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
        return currentLabel.toString();
    }


    /**
    * Set current label
    */    
    private void addLabel(String label) {
        String l = label.substring(1,label.length()-1).replace(" ", "");
        currentLabel.add(l);
        if (currentLabelId.equals("") || l.startsWith("#")) currentLabelId = "id"+l.replace("#","").replaceAll("-","");
    }


    /**
    * Reset current label
    */    
    private void resetLabel() {
        currentLabel = new LinkedList<>();
        currentLabelCounter = 0;
        currentLabelId = "";
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
    private void updateFunction(String name, List<String> nple) {
        Function f = null;

        for (String s : nple) {
            if (!tempType.containsKey(s)) { // excluding quantified variables
                return;
            }
        }

        if (!functions.containsKey(name)) {
            f = new Function(name, 0);
            functions.put(name, f);
        } else {
            f = functions.get(name);
        }

        if (nple != null) f.addTuple(nple);
    }


    /**
    * Adds Atom name and its type to pools
    */
    private void updateAtom(String name, Type type) {
        if (!tempType.containsKey(name)) { // excluding quantified variables
            atoms.add(name);

            if (type != null) {
                updateFunction("is"+type.toString(), Arrays.asList(new String[] { name }));
            }
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
        if (expr != null && !expr.isEmpty())
            smt_expr.add((currentLabelCounter == 0 ? "\n; ["+currentLabel+"]\n":"")+"(assert (! "+expr+" :named "+currentLabelId+"_"+(currentLabelCounter++)+"))");
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

        // OPTIONS
        out("(set-option :produce-unsat-cores true)\n\n");
        
        // PREAMBLE
        out("; sort\n(define-sort Atom () Int)\n\n");
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
        out("(declare-fun valueOf (Atom) Int)\n"+
            "(declare-fun nameOf (Atom) Int)\n");

        for (Function f : functions.values()) {
            out(f.getSMT());
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
            out("(assert (! (and (= "+entry.getValue()+" "+i+") (= (valueOf "+entry.getValue()+") "+i+") ) :named StringPool_"+i+"))\n");
            i++;
        }
        
        // namesOf
        out("\n; atoms names\n"+nameOfs);

        out("\n; parameters\n");
        i = 0;
        for (String expr : smt_typeparam) 
            out("(assert (! "+expr+"  :named _P"+(i++)+"))\n");

        // pre-post
        out("\n\n"+getSMTConditions("pre"));
        out("\n\n"+getSMTConditions("post"));


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
        out("(get-model)\n");
        // System.out.println("(get-model)");
        // System.out.println(owning);
    }


    /**
    * Add a type assertion for the Quantified Variable (it will be asserted to be an Atom, but after domain will be restricted by getQuantifierTypes)
    */
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
        if (NumberUtils.isNumber(s) || s.equals("true")  || s.equals("false") ) { // ToDo: consider other cases than numbers
            return s;
        } else {
            return " (valueOf " + s + " ) ";
        }
    }

    private String clean(String s) {
        return s.trim().replaceAll("\\ \\)", ")").replaceAll("\\)\\(", ") (").replaceAll("[\n\t\r]", " ").replaceAll(" +", " ");
    }

    private Map<String[], String> pre = new HashMap<>(), post = new HashMap<>();
    
    private void updateCondition(String name, String ds, String role, String expr) {
        Map<String[], String> map = null;
        if (name.equals("pre")) {
            map = pre;
        } else if (name.equals("post")) {
            map = post;
        }

        if (map != null) {
            String[] key = new String[] { ds, role };

            map.put(key, expr);
        }
    }

    private String getSMTConditions(String name) {
        String f = "";
        Map<String[], String> map = null;
        if (name.equals("pre")) {
            map = pre;
        } else if (name.equals("post")) {
            map = post;
        }

        if (map != null) {
            f = "(define-fun "+name+" ((owner Atom) (client Atom) (role Atom)) Bool \n  (if %s) \n)";

            for (Map.Entry<String[], String> entry : map.entrySet()) {
                String[] k = entry.getKey();
                
                String e = entry.getValue();
                List<String> allMatches = new ArrayList<String>();
                Matcher m = Pattern.compile("\\[(.*?)\\]").matcher(e);
                while (m.find()) {
                    allMatches.add(m.group(1));
                }

                if (allMatches.size() == 0) {
                    String smt = String.format("\n  (and (= owner %s) (= role %s))\n    (if %s true false) %s", k[0], k[1], e, "(if %s)");
                    f = String.format(f, smt);
                }  else {
                    StringBuilder sb = new StringBuilder();
                    sb.append("(exists (");
                    int i = 0;
                    for (String s : allMatches) sb.append("(a").append(i++).append(" Atom) ");
                    sb.append(") (and ");

                    i = 0;
                    for (String s : allMatches) {
                        String aName = "a"+i;

                        sb.append(" (isAttrDS ").append(aName).append(") ");
                        sb.append(" (hasAttr client ").append(aName).append(")");
                        sb.append(" (= (nameOf ").append(aName).append(") ").append(addStringPool(s)).append(")");

                        i++;
                    }
                    
                    i = 0;
                    for (String s : allMatches) {
                        e = e.replaceAll("\\["+s+"\\]", "a"+(i++));
                    }
                    sb.append(" ").append(e).append("%s))");

                    String smt = String.format("\n  (and (= owner %s) (= role %s))\n    (if %s true false) %s", k[0], k[1], String.format(sb.toString(), e), "(if %s)");
                    f = String.format(f, smt);
                }
            } 

            f = String.format(f, "true true true");
        }

        return f;
    }
}










// ------------------------------- GRAMMAR -------------------------------






program returns [String s]:    
            { init(); }
            (
                {resetLabel();}
                (l=LABEL { addLabel($l.text); })+
                ((p=pred { addExpr($p.s); })? EOP)+
            )+ 
            { printSMT(); };



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
                                                    $s = "(= (nameOf "+$t1.text+") "+addStringPool($str.text)+")";
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
                                                        updateCondition("pre", $t1.text, $r1.text, $p1.s);
                                                    }
                                                  }
     |      'Postcondition(' t1=term ','  r1=term ',' p1=pred  ')' { 
                                                    $t = Type.Bool;
                                                    $s = "";
                                                    updateCondition("post", $t1.text, $r1.text, $p1.s);
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
LABEL:      '[' '#'? ALLCHAR+ ']';


ID:         [a-z] [a-zA-Z0-9]*;


fragment 
ALLCHAR:    [a-zA-Z0-9\- ];       

DIGIT:      [0-9]+ ;             
WS:         [ \n\r\t]+ -> skip ; // skip spaces, tabs, newlines, \r (Windows)
COMMENT:    ('#'|'//') ~( '\r' | '\n' )* -> skip;
EOP:        [;]+;