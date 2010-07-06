import java.util.Hashtable;
import java.util.LinkedList;
import java.util.Enumeration;
public class ProcTable {
  Hashtable table;

  ProcTable(){
    table = new Hashtable();
  }

  ASTTipo getRet(String v){
    if (!table.containsKey(v))
      return null;
    return ((Proc) table.get(v)).ret();
  }

  void add(String a, Proc b){
    table.put(a,b);
  }

  boolean equals(String a, Proc b){
    if (table.containsKey(a))
      return ((Proc) table.get(a)).equals(b);
    else
      return false;
  }

  boolean isHere(String a){
    return table.containsKey(a);
  }

  //Chequea que la llamada a una funcion es correcta
  boolean param(String fun, LinkedList param){
    if (!table.containsKey(fun))
      return false;
    LinkedList paramFun = ((Proc) table.get(fun)).getParam();

    //Chequeo de que la cantidad de parametros de la funcion es distinto.
    if (param.size() != paramFun.size())
      return false;

    for (int i = 0; i < paramFun.size();i++){
      ASTExpr paramReal = (ASTExpr) param.get(i);
      //Chequeo de que los tipos son incompatibles
      if (!(paramReal.getTip().isCompatible((ASTTipo) paramFun.get(i))))
        return false;
    }
    return true;
  }

  boolean equals(ProcTable e){
    for  (Enumeration a = table.keys(); a.hasMoreElements() ;){
      String b = (String) a.nextElement();
      if(!e.equals(b,(Proc) table.get(b)))
        return false;
    }
    for (Enumeration a = e.table.keys();a.hasMoreElements();){
      String b = (String) a.nextElement();
      if (!(table.containsKey(b) && ((Proc) table.get(b)).equals((Proc) e.table.get(b))))
        return false;
    }
    return true;
  }

  Proc get(String name){
    return (Proc) table.get(name);
  }

}


class Proc {
  String nombre;
  ASTTipo retType;
  LinkedList param;
  ASTInstBloque cuerpo;
  int retParam;


  Proc (String nom, ASTTipo ret, LinkedList par){
    nombre = nom;
    retType = ret;
    param = par;
  }

  LinkedList getParam(){
    return param;
  }

  Proc (String nom, ASTTipo ret, LinkedList par, ASTInstBloque c){
    nombre = nom;
    retType = ret;
    param = par;
    cuerpo = c;
  }

  boolean equals(Proc b){
    return (nombre.equals(b.nombre) && retType.equals(b.retType) && b.param.equals(param));
  }

  void PtoString(){
    if (param != null)
      System.out.println(param);
    else
      System.out.println("Sin parametros");
  }

  ASTTipo ret(){
    return retType;
  }
  
  void print(){
    if (param != null)
      System.out.println(param);
  }

  void toCode(int pr, int prf){
    Global.out.println("fun" + nombre + ":");

    //Salvar enlace dinamico
    Global.out.println("sw $fp, ($sp)");
    Global.out.println("add $sp, $sp, -4");

    Global.out.println("la $fp, ($sp)");

    //Reservar variables locales, no deberia tomar en cuenta parametros, ni return address ni frame pointer.
    int tamBloque = cuerpo.tam(new tripleta(0,0,0)).espacio;

    Global.out.println("add $sp, $sp, -" + tamBloque);

    //Salvar Registros llamado
    String labelBreak = Global.nuevaEtiquetaBreak();

    //codigo Cuerpo. Cual seria la proxima instruccion aca?
    cuerpo.toCode(pr, prf, labelBreak,"fin");

    //Restaurar registro llamado
    Global.out.println(labelBreak + ":");

    //Desempilar variables locales
    Global.out.println("add $sp, $sp, " + tamBloque);

    //Restaurar enlace dinamico
    Global.out.println("add $sp, $sp, 4");
    Global.out.println("lw $fp, ($sp)");

    //Retornar
    Global.out.println("jr $ra");
  }

  //Se supone que se chequeo antes la llamada de la funcion tuviera los parametros correctos
  boolean checkParameterForLValues(LinkedList paramReales) {
    int i = 0;
    for  (Enumeration a = cuerpo.t.table.elements(); a.hasMoreElements() ;){
      info inf = (info) a.nextElement();
      if (inf.onparam && inf.tipoParametro.equals("ref")){
        ASTExpr paramReal = (ASTExpr) paramReales.get(inf.numParam);
        if (!(paramReal instanceof ASTExprLValue))
          return false;
      }
    }
    return true;
  }

}
