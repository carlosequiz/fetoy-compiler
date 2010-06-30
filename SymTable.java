import java.util.Hashtable;
import java.util.Enumeration;
import java.util.LinkedList;

class SymTable {
  Hashtable table;
  SymTable prev;
  //Necesito saber la cantidad de bits que reservan los parametros.
  int tamParam = 0;

  //@ invariant table!=null;
  //@ invariant prev!=null;

  //@ requires p!=null;
  public SymTable ( SymTable p) {
    table = new Hashtable(); prev = p;
  }

  //@ensures \result != null; 
  public Hashtable getTable(){
    return table;
  }

  //@ requires s1!=null; 
  void put(String str, info s1){
    table.put(str, s1);
  }

  //@ requires s1!=null && str!=null; 
  void put(LinkedList str, info s1){
    for (int i = 0; i < str.size();i++){
      table.put(str.get(i),s1);
    }
  }

  info find(String str){
    info found = null;
    for ( SymTable e = this ; e != null ; e = e.prev ){
      if (e.getTable()!=null)
        if  (e.getTable().get(str) instanceof info)
          found = (info) e.getTable().get(str);
      if ( found != null )
        return found;
    }
    return found;
  }

  boolean isHere(String a){
    try { 
      return table.containsKey(a); 
    } catch (Exception e) { 
      System.out.println(e); 
    }
    return false;
  }

  boolean exist(String a){
    try { 
      for ( SymTable e = this ; e !=null ; e = e.prev ){
        if (e.getTable()!=null)
          if (e.getTable().containsKey(a))
            return true;
      }
    } catch (Exception e) { 
      System.out.println(e); 
    }
    return false; 
  }

  public String toString(){
    String ret = "\nTabla de Symbolos\n";
    ret+= table.size()+"\n";
    for ( Enumeration a = table.keys(); a.hasMoreElements() ;){
      String w = (String) a.nextElement();
      if (table.get(w) instanceof info) {
        ret += w + " " + ((info) table.get(w))+"\n";
      }
    }
    return ret;
  }

  boolean empty(){
    return table.isEmpty();
  }

  int retParam(){
    return 8 + tamParam();
  }

  int tamParam(){
    tamParam = 0;
    for ( Enumeration a = table.elements(); a.hasMoreElements() ;){
      info y = (info) a.nextElement();
      if (y.onparam) {
        tamParam += y.obj.tam;
      }
    }
    return tamParam; 
  }

  boolean onProc(){
    for ( Enumeration a = table.elements(); a.hasMoreElements() ;){
      info y  = (info) a.nextElement();
      if (y.onparam) return true; 
    }
    return false;
  }

  //@ requires tr !=null;
  tripleta tam(tripleta tr){
    int regS = tr.regS;
    int regF = tr.regF;
    int esp = tr.espacio;
    // Esto antes era 0.
    if (table.isEmpty())
      return tr;
    int i = esp;
    int i2 = 12;
    info y = null;
    for ( Enumeration a = table.keys(); a.hasMoreElements() ;){
      String ria  = (String) a.nextElement();
      y = (info) table.get(ria);
      if  ( y != null && y.obj != null)
        if ( y.obj.isString()) {
          System.out.println("HAY UN STRING,revisar Symtable.java x la cantidad de memoria");
        } else {
            if (y.onparam){
              y.desp = i2;
              i2 += y.obj.tam;
            } else {
              y.desp = i;
              i += y.obj.tam;
            }
        }
    /* 
    
       Esto era asignando registros a las variables locales enteras y flotantes
        
      if ( y.obj.isEntero()){
          if (regS < Registros.S.length){
            y.desp = regS;
            y.onreg = true;
            regS++;
          }
          else{
            y.desp = i;
            i += y.obj.tam;
          }
        }
        else if (y.obj.isFloat()){
          
          if (regF < Registros.FS.length){
            y.desp = regF;
            regF++;
            y.onreg = true;
          }
          else{
            y.desp = i;
            i += y.obj.tam;
          }
        }
        else if (y.obj.isChar() || y.obj.isBool() || y.obj.isArray()){
          y.desp = i;
          i += y.obj.tam;
        }
        else if (y.obj.isString()){
        }
        else if (y.obj.isStruct()){
          y.desp = i;
          i += y.obj.tam;
        }
  */
    }
    return new tripleta(i, regS, regF);
  }

  int tamG(){
    int i = 0;
    info y =null;
    for ( Enumeration a = table.elements(); a.hasMoreElements() ;){
      y = (info) a.nextElement();
      if (y != null && y.obj!=null ){  
        if (y.obj.isString()){
          System.out.println("HAY UN STRING,revisar Symtable.java x la cantidad de memoria");
        } else {
          y.desp = i;
          i +=y.obj.tam;
        }
        y.onmain = true;
      }
    }
    return i;
  }

  /*  int onlyTam(){
      int ret = 0;
      info y;
      for ( Enumeration a = table.elements(); a.hasMoreElements() ;){
      y = (info) a.nextElement();
      if (y.obj.isNumber())
      ret +=4;
      else if (y.obj.isChar())
      ret += 2;
      else if (y.obj.isBool())
      ret += 1;
      else if (y.obj.isString())
      System.out.println("tratando de calcular el tamano de un bloque que tiene un string declarado ");
      }
      return ret;
      }*/
}
