import LogicKit


// This is a utility function, not linked directly to the syntax or the semantic
func reverse_aux (_ L: Term, _ R: Term, _ A: Term) -> Goal { // A is the accumulator
   return
      // If L is empty, the reversal is over and R takes the value of the accumulator
      (L === List.empty && R === A)
      ||
      // Otherwise, the function is called recursively with the first element of
      // L extracted and added to the accumulator (R stays untouched)
      (
         fresh{el in fresh{H in
            L === List.cons(el, H)
            &&
            delayed(reverse_aux (H, R, List.cons(el,A)))
         }}
      )
}
func reverse (_ L: Term, _ R: Term) -> Goal { // L is the original list, R the reversed one
   return
      // Call the auxiliary with an empty accumulator
      reverse_aux (L, R, List.empty)
}


// W = {whistles}
// O = {orders}
// HE = {Heidi Expressions}
// TE = {Tita Expressions}


//==============================================================================
// Heidi's syntax
//==============================================================================

// o in {deponer, dretg, sanester, davent, davos, plaun, returnar, sa fermar}
//───────────────────────────────────────────────────────────────────────────
// o in O
let deponer    = Value("deponer")
let dretg      = Value("dretg")
let sanester   = Value("sanester")
let davent     = Value("davent")
let davos      = Value("davos")
let plaun      = Value("plaun")
let returnar   = Value("returnar")
let sa_fermar  = Value("sa fermar")

// o in O
//───────────
// o in HE
//
// o in O, e in HE
//────────────────
// o;e in HE
func toHeidi (_ seq: Array<Term>) -> Term {

   var newSeq = List.empty;

   for order in seq.reversed() {
       newSeq = List.cons(order,newSeq)
   }

   return newSeq
}


//==============================================================================
// Tita's syntax
//==============================================================================

// o in {short, long, whee, who, wheet, wheeo, hee, pause}
//────────────────────────────────────────────────────────
// o in W
let short   = Value("short")
let long    = Value("long")
let whee    = Value("whee")
let who     = Value("who")
let wheet   = Value("wheet")
let wheeo   = Value("wheeo")
let hee     = Value("hee")
let pause   = Value("pause")

// o in W
//───────────
// o in TE
//
// o in W, e in TE
//────────────────
// o;e in TE
func toTita (_ seq: Array<Term>) -> Term {

   var newSeq = List.empty;

   for order in seq.reversed() {
       newSeq = List.cons(order,newSeq)
   }

   return newSeq
}


//==============================================================================
// Heidi -> Tita - 1st semantic
//==============================================================================

func heidi2tita1_aux (_ order: Term, _ translation: Term, _ acc: Term) -> Goal {
   return
      (order === List.empty && translation === acc)
      ||
      fresh{L in
         (  // deponer
            order === List.cons(deponer,L) &&
            delayed(heidi2tita1_aux(L,translation,List.cons(short,List.cons(short,List.cons(pause,acc)))))
         )
         ||
         (  // dretg
            order === List.cons(dretg,L) &&
            delayed(heidi2tita1_aux(L,translation,List.cons(whee,List.cons(who,List.cons(pause,acc)))))
         )
         ||
         (  //sanester
            order === List.cons(sanester,L) &&
            delayed(heidi2tita1_aux(L,translation,List.cons(wheet,List.cons(wheeo,List.cons(pause,acc)))))
         )
         ||
         (  //davent
            order === List.cons(davent,L) &&
            delayed(heidi2tita1_aux(L,translation,List.cons(wheet,List.cons(wheeo,List.cons(wheet,List.cons(wheet,List.cons(pause,acc)))))))
         )
         ||
         (  //davos
            order === List.cons(davos,L) &&
            delayed(heidi2tita1_aux(L,translation,List.cons(who,List.cons(hee,List.cons(who,List.cons(pause,acc))))))
         )
         ||
         (  //plaun
            order === List.cons(plaun,L) &&
            delayed(heidi2tita1_aux(L,translation,List.cons(hee,List.cons(hee,List.cons(hee,List.cons(hee,List.cons(pause,acc)))))))
         )
         ||
         (  //returnar
            order === List.cons(returnar,L) &&
            delayed(heidi2tita1_aux(L,translation,List.cons(whee,List.cons(whee,List.cons(wheet,List.cons(pause,acc))))))
         )
         ||
         (  //sa fermar
            order === List.cons(sa_fermar,L) &&
            delayed(heidi2tita1_aux(L,translation,List.cons(long,List.cons(pause,acc))))
         )
      }
}

func heidi2tita1 (_ order: Term, _ translation: Term) -> Goal {
   // order -HE-> []
   //─────────────────────
   // translation -TE-> []
   //
   // order -HE-> L;deponer, L -TE-> L'
   //──────────────────────────────────────────
   // translation -TE-> L';short;short;pause
   //
   // order -HE-> L;dretg, L -TE-> L'
   //───────────────────────────────────────
   // translation -TE-> L';whee;who;pause
   //
   // order -HE-> L;sanester, L -TE-> L'
   //──────────────────────────────────────────
   // translation -TE-> L';wheet;wheeo;pause
   //
   // order -HE-> L;davent, L -TE-> L'
   //──────────────────────────────────────────────────────
   // translation -TE-> L';wheet;wheeo;wheet;wheet;pause
   //
   // order -HE-> L;davos, L -TE-> L'
   //──────────────────────────────────────────
   // translation -TE-> L';who;hee;who;pause
   //
   // order -HE-> L;plaun, L -TE-> L'
   //──────────────────────────────────────────────
   // translation -TE-> L';hee;hee;hee;hee;pause
   //
   // order -HE-> L;returnar, L -TE-> L'
   //──────────────────────────────────────────────
   // translation -TE-> L';whee;whee;wheet;pause
   //
   // order -HE-> L;sa_fermar, L -TE-> L'
   //───────────────────────────────────────
   // translation -TE-> L';long;pause
   return
      fresh{revorder in
         reverse(order,revorder) && heidi2tita1_aux(revorder,translation,List.empty)
      }
}

func tita2heidi1 (_ order: Term, _ translation: Term) -> Goal {
   // order -TE-> o1;pause;O, o1;pause -HE-> t, O -HE-> T
   //──────────────────────────────────────────────────────────
   // translation -HE-> t;T
   //
   // order -TE-> o1;o2;pause;O, o1;o2;pause -HE-> t, O -HE-> T
   //───────────────────────────────────────────────────────────────
   // translation -HE-> t;T
   //
   // order -TE-> o1;o2;o3;pause;O, o1;o2;o3;pause -HE-> t, O -HE-> T
   //─────────────────────────────────────────────────────────────────────
   // translation -HE-> t;T
   //
   // order -TE-> o1;o2;o3;o4;pause;O, o1;o2;o3;o4;pause -HE-> t, O -HE-> T
   //───────────────────────────────────────────────────────────────────────────
   // translation -HE-> t;T
   return
      (order === List.empty && translation === List.empty)
      ||
      freshn{v in
         let t = v["t"]
         let T = v["T"]
         let o1 = v["o1"]
         let o2 = v["o2"]
         let o3 = v["o3"]
         let o4 = v["o4"]
         let O = v["O"]
         return
            translation === List.cons(t,T) &&
            (
               // 1 whistle
               (order === List.cons(o1,List.cons(pause,O))
               &&
               heidi2tita1(List.cons(t,List.empty),List.cons(o1,List.cons(pause,List.empty))))
               ||
               // 2 whistles
               (order === List.cons(o1,List.cons(o2,List.cons(pause,O)))
               &&
               heidi2tita1(List.cons(t,List.empty),List.cons(o1,List.cons(o2,List.cons(pause,List.empty)))))
               ||
               // 3 whistles
               (order === List.cons(o1,List.cons(o2,List.cons(o3,List.cons(pause,O))))
               &&
               heidi2tita1(List.cons(t,List.empty),List.cons(o1,List.cons(o2,List.cons(o3,List.cons(pause,List.empty))))))
               ||
               // 4 whistles
               (order === List.cons(o1,List.cons(o2,List.cons(o3,List.cons(o4,List.cons(pause,O)))))
               &&
               heidi2tita1(List.cons(t,List.empty),List.cons(o1,List.cons(o2,List.cons(o3,List.cons(o4,List.cons(pause,List.empty)))))))
            )
            &&
            delayed(tita2heidi1(O,T))
      }
}


//==============================================================================
// Heidi -> Tita - 2nd semantic (optimize)
//==============================================================================

func heidi2tita2_aux (_ order: Term, _ translation: Term, _ acc: Term) -> Goal {
   return
      (order === List.empty && translation === acc)
      ||
      fresh{L in
         (  // deponer
            order === List.cons(deponer,L) &&
            delayed(heidi2tita2_aux(L,translation,List.cons(wheeo,List.cons(hee,List.cons(wheet,List.cons(pause,acc))))))
         )
         ||
         (  // dretg
            order === List.cons(dretg,L) &&
            delayed(heidi2tita2_aux(L,translation,List.cons(hee,List.cons(wheet,List.cons(pause,acc)))))
         )
         ||
         (  //sanester
            order === List.cons(sanester,L) &&
            delayed(heidi2tita2_aux(L,translation,List.cons(wheet,List.cons(wheeo,List.cons(pause,acc)))))
         )
         ||
         (  //davent
            order === List.cons(davent,L) &&
            delayed(heidi2tita2_aux(L,translation,List.cons(wheet,List.cons(hee,List.cons(wheet,List.cons(pause,acc))))))
         )
         ||
         (  //davos
            order === List.cons(davos,L) &&
            delayed(heidi2tita2_aux(L,translation,List.cons(wheet,List.cons(wheeo,List.cons(wheet,List.cons(pause,acc))))))
         )
         ||
         (  //plaun
            order === List.cons(plaun,L) &&
            delayed(heidi2tita2_aux(L,translation,List.cons(wheet,List.cons(wheeo,List.cons(wheeo,List.cons(pause,acc))))))
         )
         ||
         (  //returnar
            order === List.cons(returnar,L) &&
            delayed(heidi2tita2_aux(L,translation,List.cons(wheeo,List.cons(wheet,List.cons(pause,acc)))))
         )
         ||
         (  //sa fermar
            order === List.cons(sa_fermar,L) &&
            delayed(heidi2tita2_aux(L,translation,List.cons(wheeo,List.cons(wheeo,List.cons(pause,acc)))))
         )
      }
}

func heidi2tita2 (_ order: Term, _ translation: Term) -> Goal {
   // order -HE-> []
   //─────────────────────
   // translation -TE-> []
   //
   // order -HE-> L;deponer, L -TE-> L'
   //──────────────────────────────────────────────
   // translation -TE-> L';wheeo;hee;wheet;pause
   //
   // order -HE-> L;dretg, L -TE-> L'
   //────────────────────────────────────────
   // translation -TE-> L';hee;wheet;pause
   //
   // order -HE-> L;sanester, L -TE-> L'
   //──────────────────────────────────────────
   // translation -TE-> L';wheet;wheeo;pause
   //
   // order -HE-> L;davent, L -TE-> L'
   //──────────────────────────────────────────────
   // translation -TE-> L';wheet;hee;wheet;pause
   //
   // order -HE-> L;davos, L -TE-> L'
   //────────────────────────────────────────────────
   // translation -TE-> L';wheet;wheeo;wheet;pause
   //
   // order -HE-> L;plaun, L -TE-> L'
   //────────────────────────────────────────────────
   // translation -TE-> L';wheet;wheeo;wheeo;pause
   //
   // order -HE-> L;returnar, L -TE-> L'
   //──────────────────────────────────────────
   // translation -TE-> L';wheeo;wheet;pause
   //
   // order -HE-> L;sa_fermar, L -TE-> L'
   //──────────────────────────────────────────
   // translation -TE-> L';wheeo;wheeo;pause
   return
      fresh{revorder in
         reverse(order,revorder) && heidi2tita2_aux(revorder,translation,List.empty)
      }
}

func tita2heidi2 (_ order: Term, _ translation: Term) -> Goal {
   // order -TE-> o1;o2;pause;O, o1;o2;pause -HE-> t, O -HE-> T
   //───────────────────────────────────────────────────────────────
   // translation -HE-> t;T
   //
   // order -TE-> o1;o2;o3;pause;O, o1;o2;o3;pause -HE-> t, O -HE-> T
   //─────────────────────────────────────────────────────────────────────
   // translation -HE-> t;T
   return
      (order === List.empty && translation === List.empty)
      ||
      freshn{v in
         let t  = v["t"]
         let T  = v["T"]
         let o1 = v["o1"]
         let o2 = v["o2"]
         let o3 = v["o3"]
         let O  = v["O"]
         return
            translation === List.cons(t,T) &&
            (
               // 2 whistles
               (order === List.cons(o1,List.cons(o2,List.cons(pause,O)))
               &&
               heidi2tita2(List.cons(t,List.empty),List.cons(o1,List.cons(o2,List.cons(pause,List.empty)))))
               ||
               // 3 whistles
               (order === List.cons(o1,List.cons(o2,List.cons(o3,List.cons(pause,O))))
               &&
               heidi2tita2(List.cons(t,List.empty),List.cons(o1,List.cons(o2,List.cons(o3,List.cons(pause,List.empty))))))
            )
            &&
            delayed(tita2heidi2(O,T))
      }
}

// PROOF: In the test file as the "proof()" test.


//==============================================================================
// Heidi -> Tita - 3rd semantic (accelerate)
//==============================================================================

func heidi2tita3_aux (_ order: Term, _ translation: Term, _ acc: Term) -> Goal {
   return
      (order === List.empty && translation === acc)
      ||
      fresh{L in
         (  // deponer
            order === List.cons(deponer,L) &&
            delayed(heidi2tita3_aux(L,translation,List.cons(wheeo,List.cons(hee,List.cons(wheet,acc)))))
         )
         ||
         (  // dretg
            order === List.cons(dretg,L) &&
            delayed(heidi2tita3_aux(L,translation,List.cons(hee,List.cons(wheet,acc))))
         )
         ||
         (  //sanester
            order === List.cons(sanester,L) &&
            delayed(heidi2tita3_aux(L,translation,List.cons(wheet,List.cons(wheeo,acc))))
         )
         ||
         (  //davent
            order === List.cons(davent,L) &&
            delayed(heidi2tita3_aux(L,translation,List.cons(wheet,List.cons(hee,List.cons(wheet,acc)))))
         )
         ||
         (  //davos
            order === List.cons(davos,L) &&
            delayed(heidi2tita3_aux(L,translation,List.cons(wheet,List.cons(wheeo,List.cons(wheet,acc)))))
         )
         ||
         (  //plaun
            order === List.cons(plaun,L) &&
            delayed(heidi2tita3_aux(L,translation,List.cons(wheet,List.cons(wheeo,List.cons(wheeo,acc)))))
         )
         ||
         (  //returnar
            order === List.cons(returnar,L) &&
            delayed(heidi2tita3_aux(L,translation,List.cons(wheeo,List.cons(wheet,acc))))
         )
         ||
         (  //sa fermar
            order === List.cons(sa_fermar,L) &&
            delayed(heidi2tita3_aux(L,translation,List.cons(wheeo,List.cons(wheeo,acc))))
         )
      }
}

func heidi2tita3 (_ order: Term, _ translation: Term) -> Goal {
   // order -HE-> []
   //─────────────────────
   // translation -TE-> []
   //
   // order -HE-> L;deponer, L -TE-> L'
   //──────────────────────────────────────────────
   // translation -TE-> L';wheeo;hee;wheet
   //
   // order -HE-> L;dretg, L -TE-> L'
   //────────────────────────────────────────
   // translation -TE-> L';hee;wheet
   //
   // order -HE-> L;sanester, L -TE-> L'
   //──────────────────────────────────────────
   // translation -TE-> L';wheet;wheeo
   //
   // order -HE-> L;davent, L -TE-> L'
   //──────────────────────────────────────────────
   // translation -TE-> L';wheet;hee;wheet
   //
   // order -HE-> L;davos, L -TE-> L'
   //────────────────────────────────────────────────
   // translation -TE-> L';wheet;wheeo;wheet
   //
   // order -HE-> L;plaun, L -TE-> L'
   //────────────────────────────────────────────────
   // translation -TE-> L';wheet;wheeo;wheeo
   //
   // order -HE-> L;returnar, L -TE-> L'
   //──────────────────────────────────────────
   // translation -TE-> L';wheeo;wheet
   //
   // order -HE-> L;sa_fermar, L -TE-> L'
   //──────────────────────────────────────────
   // translation -TE-> L';wheeo;wheeo
   return
      fresh{revorder in
         reverse(order,revorder) && heidi2tita3_aux(revorder,translation,List.empty)
      }
}

func tita2heidi3 (_ order: Term, _ translation: Term) -> Goal {
   // order -TE-> o1;o2;O, o1;o2 -HE-> t, O -HE-> T
   //───────────────────────────────────────────────────────────────
   // translation -HE-> t;T
   //
   // order -TE-> o1;o2;o3;O, o1;o2;o3 -HE-> t, O -HE-> T
   //─────────────────────────────────────────────────────────────────────
   // translation -HE-> t;T
   return
      (order === List.empty && translation === List.empty)
      ||
      freshn{v in
         let t  = v["t"]
         let T  = v["T"]
         let o1 = v["o1"]
         let o2 = v["o2"]
         let o3 = v["o3"]
         let O  = v["O"]
         return
            translation === List.cons(t,T) &&
            (
               // 2 whistles
               (order === List.cons(o1,List.cons(o2,O))
               &&
               heidi2tita3(List.cons(t,List.empty),List.cons(o1,List.cons(o2,List.empty))))
               ||
               // 3 whistles
               (order === List.cons(o1,List.cons(o2,List.cons(o3,O)))
               &&
               heidi2tita3(List.cons(t,List.empty),List.cons(o1,List.cons(o2,List.cons(o3,List.empty)))))
            )
            &&
            delayed(tita2heidi3(O,T))
      }
}

// It is possible to list all risked problems: Code in the test file.
