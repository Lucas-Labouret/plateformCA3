package progOfCA;

import compiledMacro.*;
import compiler.Locus;
import scala.collection.immutable.List;
import simulator.CAloops;
import simulator.CAloops2;
import simulator.PrShift;
import java.util.ArrayList;
import java.util.HashMap;
import static simulator.Util.*;

public final class GrowCA implements CAloops2 {

    public int CAmemWidth() {return 7;}

    @Override
    public ArrayList<String> theLoops(PrShift p,int[][] m) {
        ArrayList<String> bugs=new ArrayList<>();

        int[] llgrowN=m[0],
              llbugV=m[1],
              growN=m[2],
              growNNext=m[6];
        int[][] growNN= new int[][]{m[3],m[4],m[5]};




        copy(llgrowN ,growN);
        show(growN);
        redsorb.ve_1_1(p,growN,growNN);// 3 gate
        redsorb.ev_1_1(p,growNN,growNNext);// 5 gate
        memo(growNNext,llgrowN);

        return bugs;
    }

    @Override
    public HashMap<String, List<String>> textOfFields() {
        HashMap<String, List<String>> map = new HashMap<>();

        

        return map;
    }

    @Override
    public HashMap<String, String> partial() {
        HashMap<String, String> map = new HashMap<>();

        

        return map;
    }

    @Override public
    HashMap<String, List<Integer>> fieldOffset() {
        HashMap<String, List<Integer>> map = new HashMap<>(); //for layer's initialization and update, as well as displayed fields.

        map.put("llgrowN", li(0));
        map.put("llbugV", li(1));
        map.put("growN", li(2));
        map.put("growNNext", li(6));
        map.put("growNN", li(3,4,5));

        return map;
    }

    @Override
    public HashMap<String, Locus> fieldLocus() {
        HashMap<String, Locus> map = new HashMap<>();

        map.put("growNNext",compiler.Locus.locusV());
        map.put("growNN",compiler.Locus.locusE());
        map.put("llbugV",compiler.Locus.locusV());
        map.put("llgrowN",compiler.Locus.locusV());
        map.put("growN",compiler.Locus.locusV());

        return map;
    }

    @Override public HashMap<String, Integer> fieldBitSize() {
        HashMap<String, Integer> map = new HashMap<>();

;

        return map;
    }

    @Override
    public String displayableLayerHierarchy() { return "grow(growN)."; }

    @Override
    public HashMap<String, String> init() {
        HashMap<String, String> map = new HashMap<>();

        map.put("llgrowN","global");
        map.put("llbugV","false");
;

        return map;
    }

    @Override
    public int gateCount() { return 8; }
}
