import java.util.*;

abstract class ASTTipo {
  public int tam;
  abstract boolean isCompatible(ASTTipo t);

  boolean isEntero() { 
    return this instanceof ASTTipoInt;
  }
 
  boolean isFloat() { 
    return this instanceof ASTTipoFloat;
  }
 
  boolean isNumber() { 
    return isEntero() || isFloat();
  }
  
  boolean isString() { 
    return this instanceof ASTTipoString;
  }
  
  boolean isChar() { 
    return this instanceof ASTTipoChar;
  }
  
  boolean isBool() { 
    return this instanceof ASTTipoBool;
  }
 
  boolean isArray() { 
    return this instanceof ASTTipoArray;
  }
  
  boolean isStruct() { 
    return this instanceof ASTTipoStruct;
  }

  boolean isTipo() { 
    return this instanceof ASTTipoTipo;
  }

  boolean isTipoCompuesto() { 
    return this instanceof ASTTipoArray || this instanceof ASTTipoStruct;
  }

  boolean isVoid() { 
    return this instanceof ASTTipoVoid;
  }

  }

class ASTTipoFloat extends ASTTipo {
  ASTTipoFloat(){
    tam = 4;
  }

  //@ non_null
  public  String toString() {
    return "FLOAT";
  }

  public boolean equals(Object o){
    if (o instanceof ASTTipoFloat)
      return true;
    else
      return false;  
  }

  public boolean isCompatible(ASTTipo t){
    return t.isFloat();
  }
}

class ASTTipoInt extends ASTTipo {

  ASTTipoInt(){
    tam = 4;
  }

  //@ non_null
  public  String toString() {
    return "ENTERO";
  }

  public boolean equals(Object o){
    if (o instanceof ASTTipoInt)
      return true;
    else
      return false;  
  }

  public boolean isCompatible(ASTTipo t){
    return t.isFloat() || t.isEntero();
  }
}

class ASTTipoBool extends ASTTipo {
  ASTTipoBool(){
    tam = 4;
  }

  //@ non_null
  public  String toString() {
    return "BOOL";
  }

  public boolean equals(Object o){
    if (o instanceof ASTTipoBool)
      return true;
    else
      return false;  
  }

  public boolean isCompatible(ASTTipo t){
    return t.isBool();
  }
}

class ASTTipoString extends ASTTipo {
  ASTTipoString(){
  }

  //@ non_null
  public  String toString() {
    return "STRING";
  }

  public boolean equals(Object o){
    if (o instanceof ASTTipoString){
      return true;
    }
    else
      return false;  
  }

  public boolean isCompatible(ASTTipo t){
    return t.isString();
  }
}

class ASTTipoChar extends ASTTipo {
  ASTTipoChar(){
    tam = 4;
  }

  //@ non_null
  public  String toString() {
    return "CHAR";
  }

  public boolean equals(Object o){
    if (o instanceof ASTTipoChar)
      return true;
    else
      return false;  
  }

  public boolean isCompatible(ASTTipo t){
    return t.isChar();
  }
}

class ASTTipoVoid extends ASTTipo {
  ASTTipoVoid(){
  }

  //@ non_null
  public  String toString() {
    return "VOID";
  }
  public boolean isCompatible(ASTTipo t){
    return false;
  }
  public boolean equals(Object o){
    if (o instanceof ASTTipoVoid)
      return true;
    else
      return false;  
  }
}

class ASTTipoArray extends ASTTipo{
  ASTTipo subclass;
  ASTExprArit cant;

  //@ invariant subclass!=null;
  //@ invariant cant!=null;
  
  //@ requires a!=null && b!=null;
  ASTTipoArray(ASTTipo a, ASTExprArit b){
    subclass  = a;
    cant = b;
    tam = cant.getValor() * subclass.tam; 
  }

  //@ non_null
  public String toString(){
    return subclass+"["+ cant+"]";
  }

  public boolean equals(Object o){
    if (o instanceof ASTTipoArray)
      return subclass.equals(((ASTTipoArray) o).subclass);
    else
      return false;  
  }
  public boolean isCompatible(ASTTipo t){
    return false;
  }

  public int getTam(){
    return cant.getValor();
  }
}

class ASTTipoStruct extends ASTTipo{
  Hashtable st;
  structUnion union;

  //@ invariant st!=null;

  //@ requires tipo!=null;
  ASTTipoStruct(info inf, String id){
    st = new Hashtable();
    st.put(id, inf);
    union = null;
    tam = inf.obj.tam;
  }
  
  ASTTipoStruct(structUnion s){
    st = new Hashtable();
    union = s;
    tam = 0;
  }

  //@ requires tipo!=null;
  void agregar(info inf, String id){
    //le asigna un desplazamiento RELATIVO!!!
    inf.desp = tam;

    //Se agrega la informacion a la tabla de simbolos
    st.put(id, inf);

    //Se actualiza el tamaño maximo de la estructura
    tam += inf.obj.tam;
  }

  //Sirve para asignarle el desplazamiento a los elementos del union 
  void setCamposUnion(){
    info y = null;
    int max = tam;
    int i = tam;
    int actual = tam;

      for (Enumeration e = union.moreST.elements(); e.hasMoreElements();){
        Hashtable x = (Hashtable) e.nextElement();
        i = actual;
        for ( Enumeration a = x.elements(); a.hasMoreElements() ;){
          y = (info) a.nextElement();
          y.desp = i;

          i += y.obj.tam;
          if (max < i)
            max = i; 
        }
      }
      tam = max;
  }

  boolean checkAll(){
    for (Enumeration e = union.moreST.elements(); e.hasMoreElements();){
      Hashtable x = (Hashtable) e.nextElement();
      for (Enumeration w = x.keys(); w.hasMoreElements();){
        String w1 = (String) w.nextElement();
        if (st.containsKey(w1))
          return false;
      }
    }
    return true;
  }

  boolean exists(String key){
    if (st.containsKey(key))
      return true;
    
    if (union == null)
      return false;
    
    for(Enumeration e = union.moreST.elements(); e.hasMoreElements();){
      Hashtable x = (Hashtable) e.nextElement();
      if (x.containsKey(key))
        return true;
    }
    return false;
  }

  info find(String str){
    if (st.get(str) instanceof info){
      info found = (info) st.get(str) ;
       if ( found != null )
        return found;
    }
      return union.find(str);
  }


  //@ non_null
  public String toString(){
    return st.toString();
  }

  public boolean equals(Object o){
    if (o instanceof ASTTipoStruct)
      return st.equals(((ASTTipoStruct) o).st);
    else
      return false;  
  }

  public boolean isCompatible(ASTTipo t){
    return false;
  }

}


class structUnion {
  ASTTipo tipo;
  //El Discriminante se actualiza luego de creada la estructura
  String discriminante;
  Hashtable moreST;
  public int tam;

  //@ invariant st!=null;

  //@ requires tipo!=null;
  structUnion(ASTExpr opcion, Hashtable lista, int o){
    tipo = opcion.getTip();
    moreST = new Hashtable();
    moreST.put(opcion, lista);
    tam = o;
  }

  //@ requires tipo!=null;
  boolean agregar(ASTExpr o, Hashtable lista){
    // Se chequean que tengan el mismo tipo
    if (!tipo.equals(o.getTip()))
      return false;
    for (Enumeration e = moreST.elements(); e.hasMoreElements();){
      Hashtable x = (Hashtable) e.nextElement();
      for (Enumeration w = x.keys(); w.hasMoreElements();){
        String t = (String) w.nextElement();
        if (lista.containsKey(t))
          return false;
      }
    }
    moreST.put(o,lista);
    return true;
  }

  boolean exists(ASTExpr key){
    return moreST.containsKey(key);
  }

  info find(ASTExpr str){
     if ( moreST.get(str) != null )
      return (info) moreST.get(str);

    return null;
  }

  info find(String str){
    for( Enumeration e = moreST.elements(); e.hasMoreElements();){
      Hashtable q =(Hashtable) e.nextElement();
        if (q.containsKey(str))
          return (info) q.get(str);
    }
    return null;
  }


  boolean existAll(String str){
    for (Enumeration temp = moreST.elements(); temp.hasMoreElements();)
       if ( ((Hashtable) temp.nextElement()).get(str) != null )
        return true;

    return false;
  }

  void tam(int t){
    tam += t;
  }


  //@ non_null
  public String toString(){
       //String key, def="";    
      //for( Enumeration e = moreST.keys(); e.hasMoreElements(); def += ""+ key+":" + moreST.get(key)+"\n") 
        //key =  e.nextElement();
       
    return moreST.toString();
  }

}

class ASTTipoTipo extends ASTTipo{
  ASTTipo tipoSustituido;
  
  //@ invariant tipoSustituido!=null;

  //@ requires t!=null;
  ASTTipoTipo(ASTTipo t){
    tipoSustituido = t;
  }

  //@ non_null
  public String toString(){
    return tipoSustituido.toString();
  }
  
  ASTTipo getRealTipo(){
    if (tipoSustituido.isTipo())
      return ((ASTTipoTipo) tipoSustituido).tipoSustituido;
    else
      return tipoSustituido;
  }

  public boolean equals(Object o){
    if (o instanceof ASTTipoTipo)
      return tipoSustituido.equals(((ASTTipoTipo) o).tipoSustituido);
    else
      return tipoSustituido.equals(o);
  }

  public boolean isCompatible(ASTTipo t){
    return t.isTipo();
  }

}
