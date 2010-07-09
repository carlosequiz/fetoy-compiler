public class info {
  public int desp;
  public ASTTipo obj;
  boolean onreg     = false;
  boolean onmain    = false;
  boolean onparam   = false;
  boolean havedis   = false;
  boolean discri    = false;
  ASTExpr disValido = null;
  int numParam = 0;
  String tipoParametro = "valor";

  //@ invariant obj !=null;

    //@ requires o !=null;
  info(ASTTipo o){
    obj = o;
  }

  //@ requires o !=null;
  info(ASTTipo o, int f , String tip){
    obj = o;
    numParam = f;
    tipoParametro = tip;
    onparam = true;
  }

  public String toString(){
    String ret = "obj: "+obj+" desp: "+desp;
    ret = ret+"\nhd "+havedis+"\ndisValido "+disValido+"\ndiscri "+discri;
    return ret;
  }

  boolean onreg(){
    return onreg;
  }

  boolean onmain(){
    return onmain;
  }

  // Tomando en cuenta que en pr esta la direccion de la variable 
  // y en pr +1 esta la expresion a ser asignada, le asigna el valor 
  // de la expresion a la variable
  void modificaDireccion(int pr, int prf){
    String desp1 = "" , actual = "", siguiente = "", move = "", store ="";
     if (obj.isFloat()){
      actual = Registros.T[pr % Registros.maxT];
      siguiente = Registros.F[(prf + 1) % Registros.maxF];
      if (onreg)
        desp1 = Registros.FS[desp];
      move = "mov.s ";
      store = "s.s ";
    } else {
      actual = Registros.T[pr % Registros.maxT];
      siguiente = Registros.T[(pr + 1) % Registros.maxT];
      if (onreg)
        desp1 = Registros.S[desp];
      move = "move ";
      store = "sw ";
    }
    //Toma en cuenta, si la variable esta guardada en un registro 
    //o Si la variable esta en el main o si esta en la pila
    if (onreg()){
        Global.out.println(move + desp1 + ", "+ siguiente );
    } else {
        Global.out.println(store + siguiente + ", ("+ actual + ")" );
    }  
  }

  void cargaDireccion(int pr, int prf){
    int maxT = Registros.maxT;
    int maxF = Registros.maxF;
    String regT = Registros.T[pr % maxT];
    String regF = Registros.F[prf % maxF];
    String siguiente = Registros.T[(pr + 1) % maxT];
    String siguienteF = Registros.F[(prf + 1) % maxF];
   
    // Hay 3 casos. Cuando esta en el main, cuando esta en el procedimiento y cuando se guarda en un registro s
    /*
    if (onreg())
      if (obj.isEntero())
        Global.out.println("move " + regT + ", "+ Registros.S[desp]);
      else
        Global.out.println("mov.s " + regF + ","+Registros.FS[desp]);
    else 
    */

    if (onmain()){
      if (obj.isFloat()){
        Global.out.println("li "+ siguiente + " , " + desp);
        Global.out.println("la "+ regT +" , global("+ siguiente + ")");
      } else {
        Global.out.println("la "+ regT + " , global");
        Global.out.println("add " + regT + ", "+ regT + " , " + desp);
      }
    }
    else {
      String desp2 = "" + desp; 
      if(!onparam) desp2 = "-" + desp;

      if (obj.isFloat()){
        Global.out.println("add "+ siguiente + ", $fp, " + desp2);
        Global.out.println("la "+ regT + ",  0(" + siguiente +")");
      } else {
        Global.out.println("la "+ regT  + ", ($fp)");
        Global.out.println("add "+ regT  + ", "+ regT +", " + desp2);
      }
        //Si es pasaje por referencia, nos interesa la direccion que esta almacenada ahi.
        if (tipoParametro.equals("ref"))
          Global.out.println("lw " + regT + ", ("+ regT + ")");
    }
  }
  
  public boolean equals(Object o) {
    if (o instanceof info)
      return ((info) o).obj.equals(obj);
    else
      return false;
  }

}

