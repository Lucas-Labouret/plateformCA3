package compiledMacro;
import simulator.PrShift;

public class redsorb {

    public static int GateCount_ve_1_1 = 3;
    public static void ve_1_1(PrShift p, int[] ppVE, int[][] redsorbveR){
        int[] redsorbveR$h = redsorbveR[0],
              redsorbveR$d = redsorbveR[1],
              redsorbveR$ad = redsorbveR[2];

        //initialisation 
        int auxL00 = 0,
            auxL01 = 0;
        for (int i = 1; i < ppVE.length -1; i++) {
            redsorbveR$h[i-1] = (( auxL01  <<  1 ) |  auxL01 );
            auxL01= ppVE[i] ;
            redsorbveR$d[i-1] = ( auxL00  |  auxL01 );
            redsorbveR$ad[i-1] = ( auxL00  | ( auxL01  >>>  1 ));
            auxL00= auxL01 ;
        }
        p.prepareBit(redsorbveR);
    }
    public static int GateCount_ev_1_1 = 5;
    public static void ev_1_1(PrShift p, int[][] ppEV, int[] redsorbevR){
        int[] ppEV$h = ppEV[0],
              ppEV$d = ppEV[1],
              ppEV$ad = ppEV[2];

        //initialisation 
        int auxL02 = 0,
            auxL03 = 0,
            auxL04 = 0,
            tmun00 = 0;
        for (int i = 1; i < ppEV$h.length -1; i++) {
            auxL02= ppEV$h[i] ;
            auxL03= ppEV$d[i] ;
            auxL04= ppEV$ad[i] ;
            redsorbevR[i] = (((( tmun00  |  auxL02 ) |  auxL03 ) |  auxL04 ) | ( auxL02  >>>  1 ));
            tmun00=( auxL03  | ( auxL04  <<  1 ));
        }
        p.mirror(redsorbevR);
        p.prepareBit(redsorbevR);
    }}