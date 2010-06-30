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
  SymTable st;
  int retParam;


  Proc (String nom, ASTTipo ret, LinkedList par){
    nombre = nom;
    retType = ret;
    param = par;
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
    int tamBloque = cuerpo.t.tam(new tripleta(0,0,0)).espacio;

    Global.out.println("add $sp, $sp, -" + tamBloque);

    //Salvar Registros llamado
    String labelBreak = Global.nuevaEtiquetaBreak();

    //codigo Cuerpo. Cual seria la proxima instruccion aca?
    cuerpo.toCode(pr, prf, labelBreak);

    //Restaurar registro llamado
    Global.out.println(labelBreak + ":");

    //Desempilar variables locales
    Global.out.println("add $sp, $sp, " + tamBloque);

    //Restaurar enlace dinamico
    Global.out.println("add $sp, $sp, 4");
    Global.out.println("lw $fp, ($sp)");

    //Retornar
    Global.out.println("jr $ra");
    System.out.println(cuerpo.t);
  }

}
