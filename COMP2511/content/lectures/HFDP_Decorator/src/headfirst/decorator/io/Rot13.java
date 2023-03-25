package headfirst.decorator.io;

import java.io.*;

public class Rot13 extends FilterInputStream {

	public static char rotChar13(char c) {
		char newC= c;
		
		if (c >= 'a' && c <= 'm') {
			newC = (char) ((int)c + 13);
		}
		else if (c >= 'A' && c <= 'M') {
			newC = (char) ((int)c + 13);
		}
		else if (c >= 'n' && c <= 'z') {
			newC = (char) ((int)c - 13);
		}
		else if (c >= 'N' && c <= 'Z') {
			newC = (char) ((int)c - 13);
		}

		return newC;
	}

	public Rot13(InputStream in) {
		super(in);
	}

	public int read() throws IOException {
		int c = super.read();		
		char newC = rotChar13((char) c);
		//System.out.println("c is : " + (char) c + "; newC is: " + newC);
		//System.out.println("c (int) is : " + (int) c + "; newC is: " + (int) newC);

		return (c == -1 ? c : (int) newC );

		//int c = super.read();
		//char newC = rotChar13((char) c); 
		//int newInt = (int) newC;
		//return  newInt;
	}

	public int read(byte[] b, int offset, int len) throws IOException {
		int result = super.read(b, offset, len);
		for (int i = offset; i < offset + result; i++) {
			//b[i] = (byte) Character.toLowerCase((char) b[i]);
			b[i] = (byte) rotChar13((char) b[i]);
			
		}
		return result;
	}

	
}
