public class declaracion {
    private String lvalue;
    private ASTInstAsig arbol;
    private boolean tieneArbol;

    declaracion (String lvalue, ASTInstAsig arbol,boolean ba){
      this.lvalue = lvalue; this.arbol = arbol; tieneArbol = ba;
    }
  
    String getId(){
      return lvalue;
    }
  
    ASTInstAsig getArbol(){
      return arbol;
    }

    boolean tieneArbol(){
      return tieneArbol;
    }
  }
