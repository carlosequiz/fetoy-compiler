class VariableNoDeclaradaException extends Exception {

  VariableNoDeclaradaException(String var, int linea, int columna){
    super("La variable "+var+" no ha sido declarada en la linea "+linea+" columna "+columna+".");
  }
}

class FuncionVoidConReturnException extends Exception {
  FuncionVoidConReturnException (String var,int linea,int columna){
    super("La funcion "+var+" en la linea "+linea+" en la columna "+columna+", ya se declaro como void y tiene un return.");
  }

}

class FuncionNoVoidSinReturnException extends Exception {
  FuncionNoVoidSinReturnException (String var,int linea,int columna){
    super("La funcion "+var+" en la linea "+linea+" en la columna "+columna+", ya que la ultima instruccion de la funcion no es un return.");
  }

}

class ParametrosException extends Exception {
  
  ParametrosException (String var,int linea,int columna){
    super("Error en la llamada a la funcion "+var+" en la linea "+linea+" en la columna "+columna+", problemas con los parametros.");
  }
}

class SwitchException extends Exception {

  SwitchException(int linea, int columna){
    super("La comparacion con el campo discrimante debe ser del mismo tipo, en la linea "+linea+" columna "+columna+".");
  }
}

class UnionException extends Exception {

  UnionException(int linea, int columna){
    super("Error en los parametros del campo variante en la linea "+linea+" columna "+columna+".");
  }
}

class PromesaNoDeclaradaException extends Exception{
  
  PromesaNoDeclaradaException(int linea, int columna){
    super("Promesa sin cuerpo en la linea "+linea+" columna "+columna+".");
  }
}

class TiposIncompatiblesException extends Exception{
  TiposIncompatiblesException(String var, int linea, int columna){
    super("La variable "+var+" tiene una asignacion de tipos incompatibles en la linea " + linea + " columna " + columna + ".");
  }
}

class UsoIndebidoException extends Exception{
  UsoIndebidoException(int linea, int columna){
    super("Ha ocurrido un error de tipos en la linea " + linea + " columna " + columna + ".");
  }
}

class YaExisteException extends Exception {

  YaExisteException(String var, int linea, int columna){
    super("La variable "+var+" ya fue declarada en la linea "+linea+" columna "+columna+".");
  }
}

class NoIdException extends Exception{
  
  NoIdException(int linea, int columna){
    super("No puede haber id en el case en la linea "+linea+" columna "+columna+".");
  }
}

class NoReturnException extends Exception{
  NoReturnException(String var, int linea, int columna){
    super("La funcion "+var+" devuelve un parametro y no puede ser llamada como una instruccion en la linea "+linea+" columna "+columna+".");
  }

}

class FuncionNoDeclaradaException extends Exception {
    FuncionNoDeclaradaException(String var, int linea, int columna){
      super("La funcion "+var+" no fue declarada o no esta declarada correctamente en la linea "+linea+" columna "+columna+".");
    }
}

class DifTiposArrayException extends Exception {
  DifTiposArrayException(int linea, int columna){
    super("Se esta tratando de crear un arreglo con distintos tipos en la linea" + linea+", columna "+columna+".");
  }
}

class DiferentesTiposException extends Exception{

  DiferentesTiposException(int linea, int columna){
    super("Se esta tratando de crear un arreglo con distintos tipos en la linea" + linea +", columna "+columna+".");
  }
}

class MismoNombreStructException extends Exception{
  MismoNombreStructException(int linea, int columna){
    super("Se requiere que los nombres de los atributos de la estructura sean distintos en la linea "+linea+" columna "+columna+"." );
  }
}

class NoExisteAtributoException extends Exception{
  NoExisteAtributoException(String var, int linea, int columna){
    super("La variable "+var+" no ha sido declarada en la estructura en la linea "+linea+" columna "+columna+"." ); 
  }
}

class NoEsEstructuraException extends Exception{
  NoEsEstructuraException(String var, int linea, int columna){
    super("La variable "+var+" no ha sido declarada como estructura en la linea "+ linea +" columna "+ columna +"." ); 
  }
}

class TipoNoDeclaradoException extends Exception {

  TipoNoDeclaradoException(String var, int linea, int columna){
    super("El tipo "+var+" no ha sido declarado en la linea "+linea+" columna "+columna+".");
  }
}
