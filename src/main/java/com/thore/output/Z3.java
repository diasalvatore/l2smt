package com.thore.output;

import java.util.*;
import java.util.regex.*;
import org.apache.commons.lang3.math.*;



public class Z3 {
	private List<String> input, output;

	private int toInt(String s) {
		StringBuffer snum = new StringBuffer();

		for (int i = 0; i < s.length(); i++) {
		   char c = s.charAt(i);
		   if (Character.isDigit(c)) {
		   	  snum.append(c);
		   }
		}

		return NumberUtils.toInt(snum.toString());
	}

	public Z3(String input) {
		this.input = Arrays.asList(input.split("\n"));

        ProcessExecutor p = new ProcessExecutor("z3 -in");
		this.output = p.run(input);
	}

	public String raw() {
		return output.toString();
	}

	public boolean isSat() {
		if (output.size() < 1) return false;

		if (!output.get(0).toLowerCase().equals("sat")) return false;


		return true;
	}

	public String findLabel(String label) {
		for (String s : input) {
			if (s.indexOf(label) != -1) return s.replace("(assert (! ","").replace(" :named "+label+"))", "");
		}

		return "";
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();

		boolean sat = isSat();

		if (sat) {
			sb.append("SAT!\n");
			String sat_model = null;

            List<String> allMatches = new ArrayList<String>();
            List<String> responses = new ArrayList<String>();
            Matcher m = Pattern.compile("\\[unknown([a-zA-Z]+)\\]").matcher(input.toString());
            while (m.find()) {
                allMatches.add(m.group(1));
            }
	
			for (int i=2; i<output.size(); i++) {
				String o = output.get(i);
				for (int j=0; j<allMatches.size(); j++) {
					String u = allMatches.get(j);
					if (o.indexOf("(define-fun "+u, 0) != -1) {
						i++;
						int id = toInt(output.get(i));

						m = Pattern.compile("\\(assert \\(= ([a-zA-Z]+) "+id+"\\)\\)").matcher(input.toString());
						if (m.find()) {
							System.out.println(u+": "+m.group(1));
						}
					}
				}
			}		



			// System.out.println(allMatches); 

		} else {
			sb.append("unsat! :(\n");
			
			String unsat_core = null;
			if (output.size() > 1) unsat_core = output.get(1);

			if (unsat_core == null) {
				sb.append("unsat core is not available");
			} else {
				String[] labels = unsat_core.substring(1, unsat_core.length()-1).split(" ");
				sb.append("\nThe conjunction of following formulas is unsatisfable:");
				for (int i=0;i<labels.length;i++) {
					sb.append("\n"+i).append("   ").append(findLabel(labels[i]));
				}
			}

			// System.out.println(output);
		}

		return sb.toString();
	}
}