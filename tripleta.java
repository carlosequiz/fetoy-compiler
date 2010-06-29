public class tripleta {
  int espacio;
  int regS;
  int regF;

  tripleta(int e, int rs, int rf){
    espacio = e;
    regS = rs;
    regF = rf;
  }

  tripleta(){
    espacio = 0;
    regS = 0;
    regF = 0;
  }

  //@ requires t!=null;
  public void actualiza(tripleta t){
    if (t.espacio > espacio)
      espacio = t.espacio;
  }
}
