import java_cup.runtime.Symbol;
import java.io.BufferedReader;
import java.io.FileReader;
 class Yytoken {
  public int line;
  public int colu;
  public String tipo;
  public String valor;
  Yytoken (int l, int c, String t, String v){
   line = l;
   colu = c;
   tipo = t;
   valor = v;
  }

  public String toString(){

    return "Token at line "+Integer.toString(line)+" at column "+Integer.toString(colu)+" "+tipo+" value "+valor;
  }

}
%%
 
%class Lexer
%cup
%line
%column
%char
 
%{
  private Symbol symbol(int sym) {
    //System.out.println(yytext());
    return new Symbol(sym, yyline+1, yycolumn+1);
  }
 
  private Symbol symbol(int sym, Object texto) {
    //System.out.println(yytext());
    return new Symbol(sym, yyline+1, yycolumn+1, texto);
  }

 private void error(String message) {
    System.out.println("Error at line "+(yyline+1)+", column "+(yycolumn+1)+" : " + message);
  }
 
  public static void main(String argv[]) throws java.io.IOException {
    BufferedReader fr = new BufferedReader(new FileReader(argv[0]));
    Lexer yy = new Lexer(fr);
    Symbol t;
    while ((t = yy.next_token()) != null)
      System.out.println(t);
  }

  int linea(){
    return yyline+1;
  }

  int columna(){
    return yycolumn+1;
}
%}
 
ALPHA=[A-Za-z]
DIGIT=[0-9]
NONNEWLINE_WHITE_SPACE_CHAR=[\ \t\b\012]
WHITE_SPACE_CHAR=[\n\ \t\b\012]
STRING_TEXT=(\\\"|[^\n\"]|\\{WHITE_SPACE_CHAR}+\\)*
LineTerminator = \r|\n|\r\n
Comment = {TraditionalComment} | {EndOfLineComment}
TraditionalComment   = "/*" [^*] ~"*/" | "/*" "*"+ "/"
EndOfLineComment     = "//" [^\r\n]* {LineTerminator}
 
%%
 
<YYINITIAL> "read" 				{ return symbol(sym.READ);}
<YYINITIAL> "print" 					{ return symbol(sym.PRINT);}
<YYINITIAL> "return" 					{ return symbol(sym.RETURN);}
<YYINITIAL> {Comment}  					    {/* ignore */}
<YYINITIAL> "switch"				 	{ return symbol(sym.SWITCH);}
<YYINITIAL> "case" 						{ return symbol(sym.CASE);}
<YYINITIAL> ":" 							{ return symbol(sym.DOSPUNTOS);}
<YYINITIAL> "foreach" 				{ return symbol(sym.FOREACH);}
<YYINITIAL> "in" 							{ return symbol(sym.IN);}
<YYINITIAL> "for" 						{ return symbol(sym.FOR);}
<YYINITIAL> "break" 					{ return symbol(sym.BREAK);}
<YYINITIAL> "while" 					{ return symbol(sym.WHILE);}
<YYINITIAL> "if" 							{ return symbol(sym.IF);}
<YYINITIAL> "elseif" 					{ return symbol(sym.ELSEIF);}
<YYINITIAL> "else" 						{ return symbol(sym.ELSE);}
<YYINITIAL> "main" 						{ return symbol(sym.MAIN);}
<YYINITIAL> "sub"						 	{ return symbol(sym.SUB);}
<YYINITIAL> "ref" 						{ return symbol(sym.REF);}
<YYINITIAL> "++"							{ return symbol(sym.MASMAS);}
<YYINITIAL> "+="							{ return symbol(sym.MASIGUAL);}
<YYINITIAL> "--"							{ return symbol(sym.MENOSMENOS);}
<YYINITIAL> "-="							{ return symbol(sym.MENOSIGUAL);}
<YYINITIAL> "+" 							{ return symbol(sym.PLUS);}
<YYINITIAL> "-" 							{ return symbol(sym.MINUS);}
<YYINITIAL> "*" 							{ return symbol(sym.TIMES);}
<YYINITIAL> "/" 							{ return symbol(sym.DIVIDE);}
<YYINITIAL> "div" 						{ return symbol(sym.DIV);}
<YYINITIAL> "mod" 						{ return symbol(sym.MOD);}
<YYINITIAL> "void" 						{ return symbol(sym.VOID);}
<YYINITIAL> "float" 					{ return symbol(sym.FLOAT);}
<YYINITIAL> "int" 						{ return symbol(sym.ENTERO);}
<YYINITIAL> "string"		 			{ return symbol(sym.STRING);}
<YYINITIAL> "bool" 						{ return symbol(sym.BOOL);}
<YYINITIAL> "true" 						{ return symbol(sym.TRUE);}
<YYINITIAL> "false" 					{ return symbol(sym.FALSE);}
<YYINITIAL> "struct" 					{ return symbol(sym.STRUCT);}
<YYINITIAL> "union" 					{ return symbol(sym.UNION);}
<YYINITIAL> "." 					{ return symbol(sym.PUNTO);}
<YYINITIAL> "typedef" 				{ return symbol(sym.TYPEDEF);}
<YYINITIAL> "char" 						{ return symbol(sym.CHAR);}
<YYINITIAL> "&&" 							{ return symbol(sym.II);}
<YYINITIAL> "&" 							{ return symbol(sym.I);}
<YYINITIAL> "||" 							{ return symbol(sym.OO);}
<YYINITIAL> "|" 							{ return symbol(sym.O);}
<YYINITIAL> "!" 							{ return symbol(sym.NEGACION);}
<YYINITIAL> "=" 							{ return symbol(sym.IGUAL);}
<YYINITIAL> ";"				 				{ return symbol(sym.PYC);}
<YYINITIAL> "," 							{ return symbol(sym.COMA);}
<YYINITIAL> "(" 							{ return symbol(sym.LPAREN);}
<YYINITIAL> ")" 							{ return symbol(sym.RPAREN);}
<YYINITIAL> "[" 							{ return symbol(sym.LCORCHETE);}
<YYINITIAL> "]" 							{ return symbol(sym.RCORCHETE);}
<YYINITIAL> "{" 							{ return symbol(sym.LLLAVE);}
<YYINITIAL> "<" 							{ return symbol(sym.MENOR);}
<YYINITIAL> "<="	 						{ return symbol(sym.MENORIGUAL);}
<YYINITIAL> ">" 							{ return symbol(sym.MAYOR);}
<YYINITIAL> ">=" 							{ return symbol(sym.MAYORIGUAL);}
<YYINITIAL> "!=" 							{ return symbol(sym.DIFERENTE);}
<YYINITIAL> "==" 							{ return symbol(sym.IGUALIGUAL);}
<YYINITIAL> "}" 							{ return symbol(sym.RLLAVE);}
<YYINITIAL> {DIGIT}+ 					{ return symbol(sym.TKENTERO, yytext());}
<YYINITIAL> {DIGIT}+\.{DIGIT}+ { return symbol(sym.TKFLOAT, yytext());}
<YYINITIAL> \'{ALPHA}+\' 			{ return symbol(sym.TKCHAR, yytext().substring(1,2));}
<YYINITIAL> {ALPHA}({ALPHA}|{DIGIT}|_)* { return symbol(sym.ID, yytext());}
<YYINITIAL> \"[^\"]*\" { return symbol(sym.TKSTRING, yytext());}
<YYINITIAL> {NONNEWLINE_WHITE_SPACE_CHAR} {}
/* error fallback */
<YYINITIAL> .|\n 							{ /* throw new Error("Illegal character <"+ yytext()+">");*/ error("Illegal character <"+ yytext()+">"); }
 
