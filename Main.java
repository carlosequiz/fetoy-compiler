import java.io.*;
import java_cup.runtime.Symbol;
 
public class Main {
 
  /**
* * Runs the parser on an input file.
*
* @param argv the command line, argv[0] is the
* filename to run the parser on.
*
*/
  public static void main(String argv[])
    throws java.io.IOException, java.lang.Exception
  {
    //Global.out = System.out ;
    Global.out = new PrintStream(new FileOutputStream(argv[1]));
    Lexer scanner = null;
    try {
      scanner = new Lexer( new java.io.FileReader(argv[0]) );
    }
    catch (java.io.FileNotFoundException e) {
      System.out.println("File not found : \""+argv[0]+"\"");
      System.exit(1);
    }
    catch (java.io.IOException e) {
      System.out.println("Error opening file \""+argv[0]+"\"");
      System.exit(1);
    }
    catch (ArrayIndexOutOfBoundsException e) {
      System.out.println("Usage : java Main <inputfile>");
      System.exit(1);
    }
 
    /* open input files, etc. here */
    try {
      parser p = new parser(scanner);
    Symbol parse_tree = null;
 
    try {
        parse_tree = p.parse();
    } catch (YaExisteException e) {
      System.out.print(e.getMessage());
      /* do cleanup here - -
* possibly rethrow e */
    } finally {
      Global.out.close();
      /* do close out here
* */
    }
 
      // System.out.println(result.toString());
    } catch (java.lang.Exception e) {
      System.out.println("An I/O error occured while parsing : \n");
      e.printStackTrace();
      System.exit(1);
    }
 
  }
}
