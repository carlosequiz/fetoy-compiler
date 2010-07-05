import java.io.*;
import java.util.LinkedList;

class Global{
  static PrintStream out;
  static LinkedList place;
  static int plac;
  static int proxEtiqueta = 0;
  static int proxEtiquetaBreak = 0;
  static int proxMensaje = 0;
  static String error = "error";

  static String nuevaEtiqueta(){
    return "label" + proxEtiqueta++;
  }
  static String nuevaEtiquetaBreak(){
    return "break" + proxEtiquetaBreak++;
  }
  static String nuevoMensaje(){
    return "msj" + proxMensaje++;
  }
}
