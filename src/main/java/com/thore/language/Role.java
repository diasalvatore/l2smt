package com.thore.language;

import org.w3c.dom.*;
import javax.xml.transform.*;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import java.io.StringWriter;

public class Role extends AbstractLElement {
	private String type;
	private RawExpression pre, post, inv;

	public Role(Element e) {
		super(e);

		if (e != null) {
			// type
			if (e.hasAttribute("type"))
				type = e.getAttribute("type").toLowerCase().replace("consumed", "Consumes").replace("provided", "Provides");

			// conditions
			if (firstChild(e, "pre") != null) pre  = new RawExpression(firstChild(e, "pre"));
			if (pre.toString().equals("")) pre = null;

			if (firstChild(e, "post") != null) post = new RawExpression(firstChild(e, "post"));
			if (post.toString().equals("")) post = null;
			// inv  = new RawExpression(firstChild(e, "inv"));
		}
	}

	public RawExpression getPre() { return pre; }
	public RawExpression getPost() { return post; }

	public String getLContent() {
		return "";
	}

    public String getLPreamble() {
        return decorateL("IsRole("+name+");", false);
    }

    public String toString() {
        return  "R:"+name;
    }	

    public String getType() {
    	return this.type;
    }
}