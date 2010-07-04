import java.util.LinkedList;
import java.util.*;

public class Registros {
  // Registros Temporales para enteros y flotantes
  static String T[] = { "$t0", "$t1","$t2","$t3","$t4","$t5","$t6","$t7", "$t8", "$t9"};
  static int maxT = T.length;
  static String F[] = { "$f0", "$f1","$f2","$f3","$f4","$f5","$f6","$f7" , "$f8"};
  static int maxF = F.length;
  static String S[] = { "$s0", "$s1","$s2","$s3","$s4","$s5","$s6","$s7" };
  static String FS[] = { "$f10", "$f11","$f13","$f14","$f15","$f16","$f17" , "$f18"};

  //@ invariant FS != null;
  //@ invariant S != null;
  //@ invariant T != null;
  //@ invariant F != null;
  //@ invariant maxT > 0;
  //@ invariant maxF > 0;
  //@ invariant maxT == T.length;
  //@ invariant maxF == F.length;

  // Devuelve el string para salvar el registro actual 
  static String salvar(int pr){
    if (pr > maxT){
      return "add $sp, $sp, -4 \n sw "+ T[pr % maxT] +", 0($sp)";
    } else
      return "";
  };

  // Devuelve el string para restaurar el registro actual
  static String restaurar(int pr){
    if (pr > maxT){
      return "sw "+ T[pr % maxT] +", 0($sp)\n add $sp, $sp, 4";
    } else
      return "";
  };

  //@ requires pr % maxT < F.length;
  static String salvarF(int pr){
    if (pr > maxT){
      return "add $sp, $sp, -4 \n sw "+ F[pr % maxT] +", 0($sp)";
    } else
      return "";
  };

  // Devuelve el string para restaurar el registro actual
  //@ requires pr % maxT < F.length;
  static String restaurarF(int pr){
    if (pr > maxT){
      return "sw "+ F[pr % maxT] +", 0($sp)\n add $sp, $sp, 4";
    } else
      return "";
  };

  // Devuelve el string para salvar el registro actual 
  static String salvarRegistrosLlamador(int pr){
    String result = "";
    if (pr > maxT)
      for (int i = 0; i < T.length; result += "sw "+ T[i++ % maxT] +", 0($sp)\nadd $sp, $sp, -4 \n ");
    else 
      for (int i = 0; i < pr; result += "sw "+ T[i++ % maxT] +", 0($sp)\nadd $sp, $sp, -4 \n");

    return result;
  };

  // Devuelve el string para salvar el registro actual 
  static String restaurarRegistrosLlamador(int pr){
    String result = "";
    if (pr > maxT)
      for (int i = 0; i < T.length; result += " add $sp, $sp, 4\nlw "+ T[i++ % maxT] +", 0($sp)\n");
    else 
      for (int i = 0; i < pr; result += " add $sp, $sp, 4\nlw "+ T[i++ % maxT] +", 0($sp)\n");
    return result;
  };

  static void empilarParametros(LinkedList l, Proc procedimiento){
    int i = 0;

    //Necesito el reverso para empilarlo como lo dice el desp asignado.
    ArrayList al = new ArrayList();
    for  (Enumeration a = procedimiento.cuerpo.t.table.keys(); a.hasMoreElements() ; i++){
      String next = (String) a.nextElement();
      if (((info)procedimiento.cuerpo.t.find(next)).onparam){
        al.add(next);
      }
    }
    Collections.reverse(al);

    String reg = T[0];
    Global.out.println("la " + reg + ", ($sp)");

    for  (Enumeration a = Collections.enumeration(al); a.hasMoreElements() ; i++){
      String elem = (String) a.nextElement();
      info paramFormal = procedimiento.cuerpo.t.find(elem);
      if (paramFormal.tipoParametro.equals("valor"))
        codigoEPVal(paramFormal, (ASTExpr) l.get(paramFormal.numParam));
      else  
        codigoEPRef(paramFormal, (ASTExpr) l.get(paramFormal.numParam));
    }
  }

  static void codigoEPRef(info paramFormal, ASTExpr paramReal){
    String reg = T[0];
    String reg2 = T[1];
    ((ASTExprLValue) paramReal).cargaDireccion(1, 1, "algo");
    Global.out.println("sw " + reg2 + ", ( "+ reg  + ")");
    Global.out.println("add "+ reg + ", "+ reg + ", -" + 4);

    //Se actualiza finalmente el sp.
    Global.out.println("add $sp, $sp, -4");
  }

  static void codigoEPVal(info paramFormal, ASTExpr paramReal){
    String reg = T[0];
    String reg2 = T[1];

    // Depende de si es un tipo compuesto o no.
    if (!paramFormal.obj.isTipoCompuesto()){
      paramReal.toCode(1, 1, "algo");
      Global.out.println("sw " + reg2 + ", ( "+ reg  + ")");
    } else {
      //Se guardan los valores al reves, se comienza desde el final y se van copiando uno por uno.
      String reg3 = T[2];
      int tamano = paramFormal.obj.tam;
      ((ASTExprLValue) paramReal).cargaDireccion(1, 1, "algo");

      //Se inicializa en el ultimo elemento
      Global.out.println("lw " + reg3 + ", (" + reg2 + ")");
      Global.out.println("sw " + reg3 + ", (" + reg + ")");
      
      //Se va copiando uno a uno cada elemento
      for (int cont = 4; cont < tamano; cont += 4){
        Global.out.println("add " + reg + ", "+ reg +", -" + 4);
        Global.out.println("add " + reg2 + ", "+ reg2 +", -" + 4);
        Global.out.println("lw " + reg3 + ", (" + reg2 + ")");
        Global.out.println("sw " + reg3 + ", (" + reg + ")");
      }
    }
    //Se actualiza finalmente el sp.
    Global.out.println("add $sp, $sp, -" + paramFormal.obj.tam);
    Global.out.println("add "+ reg + ", "+ reg + ", -" + 4);
  }

  static void codigoDPRef(info e){
    Global.out.println("add $sp, $sp, 4");
  }

  static void codigoDPVal(info e){
    Global.out.println("add $sp, $sp, " + e.obj.tam);
  }

  static void desempilarParametros(Proc procedimiento){
    //Necesito el reverso para empilarlo como lo dice el desp asignado.
    ArrayList al = new ArrayList();
    for  (Enumeration a = procedimiento.cuerpo.t.table.keys(); a.hasMoreElements() ; ){
      String next = (String) a.nextElement();
      if (((info)procedimiento.cuerpo.t.find(next)).onparam){
        al.add(next);
      }
    }
    Collections.reverse(al);

    for  (Enumeration a = Collections.enumeration(al); a.hasMoreElements() ; ){
      String elem = (String) a.nextElement();
      info paramFormal = procedimiento.cuerpo.t.find(elem);
      if (paramFormal.tipoParametro.equals("valor"))
        codigoDPVal(paramFormal);
      else  
        codigoDPRef(paramFormal);
    }

  }
}
