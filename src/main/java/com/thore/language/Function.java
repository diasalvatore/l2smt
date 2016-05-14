package com.thore.language;

import org.w3c.dom.*;
import javax.xml.transform.*;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import java.io.StringWriter;
import java.util.*;

public class Function implements Cloneable {
    private String name;
    private int parameters;

    private Set<List<String>> tuples = new HashSet<>();

    public String getName() {
        return name;
    }

    public Function clone() {
        Function cloned = new Function(name, parameters);


        for (List<String> t : tuples) {
            List<String> cloned_list = new LinkedList<>();

            for (String val : t) {
                cloned_list.add(val);
            }
            cloned.tuples.add(cloned_list);
        }

        return cloned;
    }
    
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