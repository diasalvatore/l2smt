package com.thore.L2SMT;

import java.util.*;


public class Z3OutputParser {
	private List<String> input, output;

	public Z3OutputParser(List<String> input, List<String> output) {
		this.input = input;
		this.output = output;
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
			sb.append("SATISFABLE! ;)\n");
		} else {
			sb.append("unsatisfable! :(\n");
			
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
		}

		return sb.toString();
	}
}