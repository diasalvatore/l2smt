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
        
        sb.append("IsDS("+consumer+") && ")
          .append("IsDS("+provider+") && ")
          .append("IsRole("+role+") && ")
          .append("Consumes("+consumer+", "+role+") && ")
          .append("Provides("+provider+", "+role+") && ")
          .append("Bond("+consumer+", "+provider+", "+role+");");

        return decorateL(sb.toString(), true);
	}

    public String toString() {
        return  "R:"+name;
    }	
}