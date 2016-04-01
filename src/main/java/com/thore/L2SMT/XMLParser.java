package com.thore.L2SMT;

import org.antlr.v4.runtime.*;
import org.w3c.dom.*;
import javax.xml.parsers.*;
import java.io.*;
import java.util.*;


public class XMLParser {
	private class Signature {
		public List<String> params;
		public String output;
		public String label;

		public Signature(List<String> params, String output, String label) {
			this.params = params;
			this.output = output;
			this.label = label;
		}
		public Signature(List<String> params, String output) {
			this(params, output, null);
		}

		public String toString() {
			String s = "(" + join(params, ", ") + ")";
			if (output != null && !output.equals(""))
				s = s + " == " + output;

			return s;
		}
	}	

	private class Conditions {
		public String pre, post, inv;

		public Conditions(String pre, String post, String inv) {
			this.pre = pre.replaceAll("[-+.:,\t\n\r]","");
			this.post = post.replaceAll("[-+.:,\t\n\r]","");
			this.inv = inv.replaceAll("[-+.:,\t\n\r]","");
		}

		public String replaceBind(String rep) {
			String ret = "";
			if (this.pre != null && this.pre.length() > 0) {
				ret += this.pre + ";\n";
			}
			
			if (this.post != null && this.post.length() > 0) {
				ret += this.post + ";\n";
			}
			
			if (this.inv != null && this.inv.length() > 0) {
				ret += this.inv + ";\n";
			}

			return ret.replace("^", rep.replace("DS","AD")+".");
		}

		public String toString() {
			return "("+pre+","+post+","+inv+")";
		}
	}

	public class NameWSource {
		public String name;
		public String source;
		public int line;

		public NameWSource(String name, String source, int line) {
			this.name = name;
			this.source = source;
			this.line = line;

			// System.out.println("SOURCE: "+source);
		}

		public NameWSource(String name, String source) {
			this(name, source, -1);
		}

        public boolean equals(Object o) {
            if (o == null) return false;
            if (o.getClass() != this.getClass()) return false;
                
            NameWSource f = (NameWSource)o;
            return (f.name.toLowerCase().equals(this.name.toLowerCase()));
        }
	}

	private Map<String, Set<String>> atoms = new HashMap<>();
	private Map<String, List<String>> formulas = new HashMap<>();
	private Map<String, List<Signature>> functions = new HashMap<>();
	private Map<String, Conditions> ds_conditions = new HashMap<>();
	private String file;
	private boolean incremental_verification = false;

	private String addAtom(String type, NameWSource nws, String owner) { 
        if (!atoms.containsKey(type)) atoms.put(type, new HashSet<String>());      

        if (owner == null) {
        	nws.name = type.trim().toUpperCase()+"."+nws.name.trim().toLowerCase();
        } else {
        	nws.name = owner.replace("DS","AD") + "." + nws.name.trim().toLowerCase();
        }
		atoms.get(type).add(nws.name); 

		return nws.name;
	}

	private String addFormula(String label, String f) { 
        if (!formulas.containsKey(label)) formulas.put(label, new LinkedList<String>());      

        formulas.get(label).add(f.trim()); 

		return f;
	}


	private void addFunction(String fun, Signature sig) {
		fun = fun.substring(0, 1).toUpperCase() + fun.substring(1);
        if (!functions.containsKey(fun))
        	functions.put(fun, new LinkedList<Signature>());      
        
        functions.get(fun).add(sig);
	}



	public XMLParser(String file) throws Exception {
		this.file = file;
	}
	

	public LabeledSource parse() throws Exception {
		DocumentBuilderFactory builderFactory = DocumentBuilderFactory.newInstance();
		DocumentBuilder builder = null;

	    builder = builderFactory.newDocumentBuilder();
		Document document = builder.parse(new FileInputStream(file));
		Element element = document.getDocumentElement();
		NodeList nodes = element.getChildNodes();

		for (int i=0; i<nodes.getLength(); i++) {
			Node node = nodes.item(i);

			if (node instanceof Element) {
			    Element child = (Element) node;
			    switch (child.getNodeName()) {
			    	case "roles":
			    		parseRoles(child, null);
			    		break;
			    	case "design-solutions":
						parseDesignSolutions(child);
			    		break;
			    	case "attributes":
						parseAttributes(child, "AE", null);
			    		break;
			    	case "bindings":
						parseBindings(child);
			    		break;
			    	case "constraints":
						parseConstraints(child);
			    		break;
			    }
			}
		}

		return getLabeledSource();
	}

	public LabeledSource getLabeledSource() {
		LabeledSource ls = new LabeledSource();

		// ATOMS
		LabeledSource.LabeledGroup lg = ls.new LabeledGroup("Atoms");
		for (Map.Entry<String, Set<String>> e : atoms.entrySet()) {
			String t = "Is"+transType(e.getKey())+"(";
			lg.addLine(t+    join(e.getValue(), ") && "+t)    +");");
		}
		ls.addUnorderedGroup(lg);
		
		lg = ls.new LabeledGroup("System Status");
		for (Map.Entry<String, List<Signature>> f : functions.entrySet()) {
			StringBuilder sb = new StringBuilder();
			boolean first = true;
			for (Signature s : f.getValue()) {
				if (s.label != null && !s.label.equals("")) {
					sb.append("\n[").append(s.label).append("]\n");
				}
				if (first) {
					first = false;
				} else {
					sb.append(" && ");
				}
				sb.append(f.getKey()).append(s.toString());
			}
			sb.append(";");
			lg.addLine(sb.toString());
		}
		ls.addUnorderedGroup(lg);

		for (Map.Entry<String, List<String>> f : formulas.entrySet()) {
			lg = ls.new LabeledGroup(f.getKey());
			lg.addLine(join(f.getValue(), ";\n") + ";");
			
			if (this.incremental_verification)
				ls.addOrderedGroup(lg);
			else
				ls.addUnorderedGroup(lg);
		}

		// System.out.println(join(atoms, " && "));
		// System.out.println(functions);
		// System.out.println(__output.toString());

		return ls;
	}

	private StringBuilder __output = new StringBuilder();
	private void o(String s) {
		__output.append(s).append("\n");
		// System.out.println(s);
	}

	private void parseDesignSolutions(Element element) {
		NodeList nodes = element.getElementsByTagName("design-solution");

		for (int i=0; i<nodes.getLength(); i++) {
			Element e = (Element)nodes.item(i);
			
			String ds = addAtom("DS", new NameWSource(e.getAttribute("name"), element.toString()), null);
			parseRoles(firstChild(e, "roles"), ds);
			parseAttributes(firstChild(e, "attributes"), "AD", ds);


			// addRole(nodes.item(i).getTextContent());
		}
	}
	
	private void parseConstraints(Element element) {
		NodeList nodes = element.getElementsByTagName("constraint");

		for (int i=0; i<nodes.getLength(); i++) {	
			Element e = (Element)nodes.item(i);
			String label = "constraint "+(e.hasAttribute("label") ? e.getAttribute("label") : i);

			addFormula(label, e.getTextContent());
		}
	}

	private void parseBindings(Element element) {
		NodeList nodes = element.getElementsByTagName("binding");
		this.incremental_verification = (element.hasAttribute("incrementalVerification") && !element.getAttribute("incrementalVerification").toLowerCase().equals("false"));

		for (int i=0; i<nodes.getLength(); i++) {
			Element e = (Element)nodes.item(i);
			String label = "binding "+(e.hasAttribute("label") ? e.getAttribute("label") : i);
			String c = addAtom("DS",new NameWSource(e.getAttribute("consumer"), e.toString()), null);
			String p = addAtom("DS",new NameWSource(e.getAttribute("provider"), e.toString()), null);
			String r = addAtom("R", new NameWSource(e.getAttribute("role"), e.toString()), null);
			String consumerConditionsKey = c+"-"+r;
			String providerConditionsKey = p+"-"+r;

			addFormula(label, "Bond("+c+","+p+","+r+")");			

			// System.out.println(ds_conditions);
			// System.out.println(consumerConditionsKey);
			// System.out.println(providerConditionsKey);
			if (ds_conditions.get(consumerConditionsKey) != null) {
				// System.out.println(ds_conditions.get(consumerConditionsKey));
				String f = ds_conditions.get(consumerConditionsKey).replaceBind(p);
				// System.out.println("===>"+f);
				if (f != null && !f.equals(""))	addFormula(label, f);
			}
			if (ds_conditions.get(providerConditionsKey) != null) {
				// System.out.println(ds_conditions.get(providerConditionsKey));
				String f = ds_conditions.get(providerConditionsKey).replaceBind(c);
				if (f != null && !f.equals(""))	addFormula(label, f);
				// System.out.println("===>"+f);
			}
		}
	}
	

	private void parseAttributes(Element element, String metatype, String owner) {
		NodeList nodes = element.getElementsByTagName("attribute");

		for (int i=0; i<nodes.getLength(); i++) {
			Element attribute_element = (Element)nodes.item(i);
			String a = addAtom(metatype, new NameWSource(attribute_element.getAttribute("name"), element.toString()), owner);

			// metatype
			if (metatype != null) {
				addFunction("is"+transType(metatype), new Signature(Arrays.asList( new String[] { a }), null));
			}
			
			// owner
			if (owner != null) {
				addFunction("hasAttr",new Signature(Arrays.asList( new String[] { owner, a }), null));
			}

			// type
			String type = transType(attribute_element.hasAttribute("type") ? attribute_element.getAttribute("type") : "String");
			addFunction("is"+type, new Signature(Arrays.asList( new String[] { a }), null));

			// value
			if (!attribute_element.getTextContent().equals("")) {
				// addFunction("valueOf",new Signature(Arrays.asList( new String[] { a } ), (type.equals("String") ? "\""+attribute_element.getTextContent()+"\"" : attribute_element.getTextContent()) ));
				addFormula("values", a+" == "+(type.equals("String") ? "\""+attribute_element.getTextContent()+"\"" : attribute_element.getTextContent())); //new Signature(Arrays.asList( new String[] { a } ), (type.equals("String") ? "\""+attribute_element.getTextContent()+"\"" : attribute_element.getTextContent()) ));
			}
		}
	}

	private void parseRoles(Element element, String ds) {
		NodeList nodes = element.getElementsByTagName("role");

		for (int i=0; i<nodes.getLength(); i++) {
			Element role_element = (Element)nodes.item(i);
			String r = addAtom("R", new NameWSource(role_element.getAttribute("name"), role_element.toString()), null);

			if (ds != null && role_element.hasAttribute("type")) {
				String type = role_element.getAttribute("type").toLowerCase().replace("consumed", "consumes").replace("provided", "provides");
				if (type.equals("consumed") || type.equals("provided")) {
					addFunction(type, new Signature(Arrays.asList(new String[] { ds, r }), null));
				}
				
				ds_conditions.put(ds+"-"+r, new Conditions(firstChildText(role_element, "pre"), firstChildText(role_element, "post"), firstChildText(role_element, "inv")));
			}
		}
	}


	private String transType(String type) {
		type = type.toLowerCase();

		if (type.startsWith("int"))         return "Int";
		else if (type.startsWith("real"))   return "Real";
		else if (type.startsWith("bool"))   return "Bool";
		else if (type.startsWith("string")) return "String";
		else if (type.startsWith("ae"))     return "AttrE";
		else if (type.startsWith("ad"))     return "AttrDS";
		else if (type.startsWith("ds"))     return "DS";
		else if (type.startsWith("r"))      return "Role";

		return "";
	}

	private Element firstChild(Element element, String name) {
		NodeList nodes = element.getElementsByTagName(name);

		return (nodes.getLength() > 0 ? (Element)nodes.item(0) : null);
    }

    private String firstChildText(Element element, String name) {
    	Element e = firstChild(element, name);

    	return (e == null ? "" : e.getTextContent()); 
    }

    private String join(Collection<String> list, String conjunction) {
		StringBuilder sb = new StringBuilder();
		boolean first = true;
		
		for (String item : list) {
			if (first)
				first = false;
			else
				sb.append(conjunction);
			sb.append(item);
		}

		return sb.toString();
	}
}