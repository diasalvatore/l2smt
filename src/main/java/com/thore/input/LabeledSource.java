package com.thore.input;

import java.util.*;

public class LabeledSource {
	public class LabeledGroup {
		private String label;
		private List<String> lines = new ArrayList<>();
		
		public LabeledGroup(String label) {
			this.label = label;
		}

		public void addLine(String line) {
			lines.add(line);
		}

		public String toString() {
			StringBuilder sb = new StringBuilder();
			sb.append("[").append(label).append("]\n");

			for (String l : lines) {
				sb.append(l).append("\n");
			}

			return sb.toString();
		}

		public String getLabel() {
			return label;
		}
	}

	private List<LabeledGroup> unordered_source = new LinkedList<>();
	private Map<Integer, LabeledGroup> ordered_source = new TreeMap<>();
	private int ordered_size = 0;

	public int getOrderedSize() {
		return ordered_size;
	}

	public void addUnorderedGroup(LabeledGroup lg) {
		unordered_source.add(lg);
	}

	public void addOrderedGroup(LabeledGroup lg) {
		ordered_source.put(ordered_size++, lg);
	}

	public String toString() {
		return getOrderedCode(ordered_size+1);
	}
	
	public String getOrderedCode(int limit) {
		StringBuilder sb = new StringBuilder();

		for (LabeledGroup lg : unordered_source) {
			sb.append(lg.toString()).append("\n");
		}

		int i = 0;
		for (LabeledGroup lg : ordered_source.values()) {
			if (i < limit) sb.append(lg.toString()).append("\n");
			i++;
		}

		return sb.toString();
	}	

	public String getOrderedLabels(int limit) {
		StringBuilder sb = new StringBuilder();

		for (LabeledGroup lg : unordered_source) {
			sb.append("'").append(lg.getLabel()).append("'").append(", ");
		}

		int i = 0;
		for (LabeledGroup lg : ordered_source.values()) {
			if (i < limit) sb.append("'").append(lg.getLabel()).append("'").append((i+1<limit?", ":" "));
			i++;
		}

		return sb.toString();
	}
}