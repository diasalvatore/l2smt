package com.thore.language;

import org.w3c.dom.*;
import javax.xml.transform.*;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import java.io.StringWriter;
import java.util.*;
import java.util.regex.*;
import org.apache.logging.log4j.*;

public class SystemState implements Cloneable {
    private Logger logger = LogManager.getFormatterLogger(getClass().getName());
    private Type[] mutual_exclusive =  { Type.Bool, Type.Int, Type.Real, Type.String, Type.Role, Type.DS };
    
    // the following should be cloned
    private Map<String, Function> functions;
    private Set<String>  atoms = new HashSet<>();
    private List<String> smt_typeparam = new LinkedList<>();
    private List<String> smt_expr = new LinkedList<>();
    private Map<String[], String> pre = new HashMap<>(), post = new HashMap<>();
    private Map<String, String> stringPool = new TreeMap<>();
    private Map<String, String> resolved = new TreeMap<>();
    private Map<String, String> novar = new TreeMap<>();

    public boolean atomsContains(String a) {
        return atoms.contains(a);
    }

    public void addResolved(String unknown, String res) {
        resolved.put(unknown, res);
    }

    public void addNoVar(String unknown, String res) {
        novar.put(unknown, res);
    }

    public void removeResolved(String unknown) {
        resolved.remove(unknown);
    }

    public String getVar(String smt) {
        String sat_model = null;
        Map<String, String> resolved = new HashMap<>();
        List<String> allMatches = new ArrayList<String>();
        List<String> responses = new ArrayList<String>();
        //logger.debug("SMT: "+smt);
        Matcher m = Pattern.compile("(\\$[a-zA-Z]+)").matcher(smt);
        while (m.find()) {
            //logger.debug("Found var: "+m.group(1));
            allMatches.add(m.group(1));
        }    

        return (allMatches.size()>0 ? allMatches.get(0) : null);
    }

    public SystemState() {
        functions = new HashMap<>();

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

    public void updateCondition(String name, String ds, String role, String expr) {
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


    /**
    * Returns true if two type are incompatible
    */
    private boolean areMutualExclusive(Type t1, Type t2) {
        return ( (Arrays.asList(mutual_exclusive).contains(t1) && Arrays.asList(mutual_exclusive).contains(t2)) );
    }

    public void updateFunction(String name, List<String> nple) {
        Function f = null;

        if (!functions.containsKey(name)) {
            f = new Function(name, 0);
            functions.put(name, f);
        } else {
            f = functions.get(name);
        }

        if (nple != null) f.addTuple(nple);
    }
    
    public void updateAtom(String name, Type type) {
        atoms.add(name);

        if (type != null) {
            updateFunction("is"+type.toString(), Arrays.asList(new String[] { name }));
        }
    }


    public SystemState clone() {
        SystemState cloned = new SystemState();

        // private Map<String, Function> functions;
        for (Map.Entry<String, Function> entry : functions.entrySet()) {
            cloned.functions.put(entry.getKey(), entry.getValue().clone());
        } 
        
        // private Set<String>  atoms = new HashSet<>();
        for (String entry : atoms) {
            cloned.atoms.add(entry);
        }
        
        // private List<String> smt_typeparam = new LinkedList<>();
        for (String entry : smt_typeparam) {
            cloned.smt_typeparam.add(entry);
        }

        // private List<String> smt_expr = new LinkedList<>();
        for (String entry : smt_expr) {
            cloned.smt_expr.add(entry);
        }

        // private Map<String[], String> pre = new HashMap<>(), post = new HashMap<>();
        for (Map.Entry<String[], String> entry : pre.entrySet()) {
            cloned.pre.put(entry.getKey(), entry.getValue());
        }
        for (Map.Entry<String[], String> entry : post.entrySet()) {
            cloned.post.put(entry.getKey(), entry.getValue());
        }

        // private Map<String, String> stringPool = new TreeMap<>();
        for (Map.Entry<String, String> entry : stringPool.entrySet()) {
            cloned.stringPool.put(entry.getKey(), entry.getValue());
        }

        return cloned;
    }


    public void addExpr(String expr) {
        if (expr != null && !expr.isEmpty())
            smt_expr.add(expr);
    }

    public String getSMT() {
        StringBuilder output = new StringBuilder();
        String tmp;
        int i;

        // OPTIONS
        output.append("(set-option :produce-unsat-cores true)\n\n");
        
        // PREAMBLE
        output.append("; sort\n(define-sort Atom () Int)\n\n");
        output.append("\n; atoms\n");
        
        // atoms 
        String nameOfs = "";
        for (String atom : atoms) {
            output.append("(declare-const "+atom+" Atom)\n");

            // nameOfs
            int lio = atom.lastIndexOf('.');
            String tmp_name = (lio != -1 ? atom.substring(lio+1) : atom);
            nameOfs += "(assert (= (nameOf "+atom+") "+addStringPool(tmp_name)+"))\n";
        }
        for (String res : resolved.keySet()) {
            output.append("(declare-const "+res.replace("$","")+" Atom)\n");
        }

        // strings
        for (Map.Entry<String, String> entry : stringPool.entrySet()) {
            output.append("(declare-const "+entry.getValue()+" Atom) ; "+entry.getKey()+"\n");        
        }

        // predicates
        output.append("\n; predicates\n");
        output.append("(declare-fun valueOf (Atom) Int)\n"+
            "(declare-fun nameOf (Atom) Int)\n");

        for (Function f : functions.values()) {
            output.append(f.getSMT());
        }

        // atoms unique val
        output.append("\n; atoms unique val \n");
        i = 0;
        for (String atom : atoms) {
            output.append("(assert (= "+atom+" "+i+"))\n");
            // output.append("(assert (= (valueOf "+atom+") "+i+"))\n");
            i++;
        }

        // strings unique val
        for (Map.Entry<String, String> entry : stringPool.entrySet()) {
            output.append("(assert (! (and (= "+entry.getValue()+" "+i+") (= (valueOf "+entry.getValue()+") "+i+") ) :named StringPool_"+i+"))\n");
            i++;
        }
        
        // namesOf
        output.append("\n; atoms names\n"+nameOfs);

        output.append("\n; parameters\n");
        i = 0;
        for (String expr : smt_typeparam) 
            output.append("(assert (! "+expr+"  :named _P"+(i++)+"))\n");

        // pre-post
        output.append("\n\n"+getSMTConditions("pre"));
        output.append("\n\n"+getSMTConditions("post"));


        // uninterpreted functions properties

        // every atom has a type
        output.append("\n; ---== Properties ==---\n");
        tmp = "";
        // for (Type t : mutual_exclusive) tmp += " (= (is"+t+" x) true)";
        // output.append("\n; every atom has a type\n(assert (forall ((x Atom)) (or"+tmp+")))\n");


        // the following predicates are mutually exclusive
        tmp = "";
        output.append("\n; the following predicates are mutually exclusive\n");
        for (Type t : mutual_exclusive) {
            tmp += "(assert (! (forall ((x Atom)) (=> (= (is"+t+" x) true) (and";
            for (Type t2 : mutual_exclusive) if (t2 != t) tmp += " (= (is"+t2+" x) false)";
            tmp += "))) :named multipleType_"+t+"))\n";
        }
        output.append(tmp);



        // AttrDS haven't multiple owners
        //output.append("\n; AttrDS haven't multiple owners\n"+
        //    "(assert (! (forall ((x Atom) (y Atom)) (=> (and (= (isDS x) true) (= (hasAttr x y) true)) (forall ((z Atom)) (=> (and (= (isDS z) true) (not (= x z))) (not (= (hasAttr z y) true)) )))) :named _UniqueHasAttr)) \n");

        output.append("\n\n; ---=== User Defined Assertions ===---\n ");

        output.append("\n; <no>\n ");
        for (Map.Entry<String, String> no : novar.entrySet()) {
            output.append("(not (= "+no.getKey()+" "+no.getValue()+"))\n");
        }
        output.append("\n; </no>\n ");

        for (String expr : smt_expr) {
            // ; [[?unknownordinatore]]
            // (assert (! (exists ((ordinatore Atom) ) (and (= (isDS ordinatore) true)  (pre ordinatore binarySearch sorter))) :named id?unknownordinatore_0))
            Matcher m = Pattern.compile("\\[\\?unknown([a-zA-Z]+)\\]").matcher(expr);
            if (m.find()) {
                String noVarName  = m.group(1);
                String noVarValue = novar.get(noVarName);
                if (noVarValue != null) {
                    expr = expr.replace("(and ", "(and (not (= "+noVarName+" "+noVarValue+")) ");
                }
            }


            String var = getVar(expr);
            
            // logger.debug("["+smt_expr.size()+"] "+resolved);
            if (var != null) {
                String replace = resolved.get(var.replace("$",""));
                if (replace != null) {
                    // logger.debug("Substituting: "+var+" with "+replace);
                    output.append(expr.replace(var,replace)).append(" ; ").append(var).append("\n");    
                } else {
                    // logger.debug("Substituting: "+var+"failed");
                    output.append(";").append(expr).append("\n");  
                } 
            } else {
                output.append(expr+"\n");    
            }

        }

        output.append("\n\n(check-sat)\n");
        output.append("(get-unsat-core)\n");
        output.append("(get-model)\n");
        // System.out.println("(get-model)");
        // System.out.println(owning);

        return output.toString();
    }

    /**
    * Adds a string to the pool and returns an uid
    */
    public String addStringPool(String s) {
        s = s.replace("\"","");
        if (!stringPool.containsKey(s)) {
            stringPool.put(s, "string"+stringPool.size());
        } 

        return stringPool.get(s);
    }
}