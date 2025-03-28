package com.mycompany.jena.utils;

public class Counter {

	private int count;

	public Counter(int i)
	{
		this.count = i;
	}

	public void increase() {
		this.count += 1;
	}

	public void increase(int c) {
		this.count += c;
	}

	public int increaseUse() {
		this.count += 1;
		return this.count - 1;
	}

	public void decrease() {
		this.count -= 1;
	}

	public int getValue() {
		return this.count;
	}

	public int hashCode() {
		return this.count;
	}

	public boolean equals(Object obj) {
		if (!(obj instanceof Counter)) {
			return false;
		}

		return this.count == ((Counter)obj).count;
	}

	//public String toString() {
	//	return this.count;
	//}
}


