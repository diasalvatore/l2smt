package com.thore.language;

import org.w3c.dom.*;
import javax.xml.transform.*;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import java.io.StringWriter;

public class Binding extends AbstractLElement {
	private String role;
	private String consumer, provider;

	public Binding(Element e) {
		super(e);

		if (e != null) {
			role = e.getAttribute("role");
			consumer = e.getAttribute("consumer");
			provider = e.getAttribute("provider");
		}
	}

	public String getLContent() {
        StringBuilder sb = new StringBuilder();
        
        sb.append("IsDS("+consumer+");\n ")
          .append("IsDS("+provider+");\n ")
          .append("IsRole("+role+");\n ")
          .append("Consumes("+consumer+", "+role+");\n ")
          .append("Provides("+provider+", "+role+");\n ")
          .append("Bond("+consumer+", "+provider+", "+role+");\n");

        return decorateL(sb.toString(), true);
	}

    public String toString() {
        return  "R:"+name;
    }	
}