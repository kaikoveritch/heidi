import XCTest
import Foundation
import LogicKit
@testable import heidi

// Wrapper struct and resultsOf function
// Shamefully ripped off from the minotaurTests file in order to test the
// results in a manageable manner.

struct Wrapper : Equatable, CustomStringConvertible {
  let term : Term

  var description: String {
      return "\(self.term)"
  }

  static func ==(lhs: Wrapper, rhs: Wrapper) -> Bool {
    return (lhs.term).equals (rhs.term)
  }

}

func resultsOf (goal: Goal, variables: [Variable]) -> [[Variable: Wrapper]] {
    var result = [[Variable: Wrapper]] ()
    for s in solve (goal) {
        let solution  = s.reified ()
        var subresult = [Variable: Wrapper] ()
        for v in variables {
            subresult [v] = Wrapper (term: solution [v])
        }
        if !result.contains (where: { x in x == subresult }) {
            result.append (subresult)
        }
    }
    return result
}


// Tests

class heidiTests: XCTestCase {

   // Display for readability
   func startTests() {
      print("\n[Starting tests]\n")
   }

//==============================================================================
// Syntax tests
//==============================================================================

   // Test heidi sequences
   func testHeidiSeq() {
      let res = toHeidi([deponer,davent,plaun,deponer,dretg])
      let expected = List.cons(deponer,List.cons(davent,List.cons(plaun,List.cons(deponer,List.cons(dretg,List.empty)))))
      XCTAssert(res.equals(expected),"Wrong sequence.")
   }

   // Test tita sequence
   func testTitaSeq() {
      let res = toTita([whee,whee,who,pause,wheet,short,long,pause])
      let expected = List.cons(whee,List.cons(whee,List.cons(who,List.cons(pause,List.cons(wheet,List.cons(short,List.cons(long,List.cons(pause,List.empty))))))))
      XCTAssert(res.equals(expected),"Wrong sequence.")
   }

//==============================================================================
// Semantic 1 tests
//==============================================================================

   // Test Heidi -> Tita
   func testHeidi2Tita1() {
      let A = Variable(named: "A")

      var from = toHeidi([davent,deponer,returnar])
      var to = toTita([wheet,wheeo,wheet,wheet,pause,short,short,pause,whee,whee,wheet,pause])
      var prob = heidi2tita1(from,A)
      var results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      if results.count == 1 {
         XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: to), "Result is false")
      }

      from = toHeidi([plaun,plaun])
      to = toTita([hee,hee,hee,hee,pause,hee,hee,hee,hee,pause])
      prob = heidi2tita1(from,A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      if results.count == 1 {
         XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: to), "Result is false")
      }

      from = toHeidi([sa_fermar,returnar,plaun,davos,davent,sanester,dretg,deponer])
      to = toTita(
         [
         long,pause,
         whee,whee,wheet,pause,
         hee,hee,hee,hee,pause,
         who,hee,who,pause,
         wheet,wheeo,wheet,wheet,pause,
         wheet,wheeo,pause,
         whee,who,pause,
         short,short,pause
         ]
      )
      prob = heidi2tita1(from,A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      if results.count == 1 {
         XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: to), "Result is false")
      }
   }

   // Test Tita -> Heidi
   func testTita2Heidi1() {
      let A = Variable(named: "A")

      var from = toTita([wheet,wheeo,wheet,wheet,pause,short,short,pause,whee,whee,wheet,pause])
      var to = toHeidi([davent,deponer,returnar])
      var prob = tita2heidi1(from,A)
      var results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      if results.count == 1 {
         XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: to), "Result is false")
      }

      from = toTita([hee,hee,hee,hee,pause,hee,hee,hee,hee,pause])
      to = toHeidi([plaun,plaun])
      prob = tita2heidi1(from,A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      if results.count == 1 {
         XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: to), "Result is false")
      }

      from = toTita(
         [
            long,pause,
            whee,whee,wheet,pause,
            hee,hee,hee,hee,pause,
            who,hee,who,pause,
            wheet,wheeo,wheet,wheet,pause,
            wheet,wheeo,pause,
            whee,who,pause,
            short,short,pause
         ]
      )
      to = toHeidi([sa_fermar,returnar,plaun,davos,davent,sanester,dretg,deponer])
      prob = tita2heidi1(from,A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      if results.count == 1 {
         XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: to), "Result is false")
      }
   }

//==============================================================================
// Semantic 2 tests
//==============================================================================

   // Test Heidi -> Tita
   func testHeidi2Tita2() {
      let A = Variable(named: "A")

      var from = toHeidi([davent,deponer,returnar])
      var to = toTita([wheet,hee,wheet,pause,wheeo,hee,wheet,pause,wheeo,wheet,pause])
      var prob = heidi2tita2(from,A)
      var results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      if results.count == 1 {
         XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: to), "Result is false")
      }

      from = toHeidi([plaun,plaun])
      to = toTita([wheet,wheeo,wheeo,pause,wheet,wheeo,wheeo,pause])
      prob = heidi2tita2(from,A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      if results.count == 1 {
         XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: to), "Result is false")
      }

      from = toHeidi([sa_fermar,returnar,plaun,davos,davent,sanester,dretg,deponer])
      to = toTita(
         [
         wheeo,wheeo,pause,
         wheeo,wheet,pause,
         wheet,wheeo,wheeo,pause,
         wheet,wheeo,wheet,pause,
         wheet,hee,wheet,pause,
         wheet,wheeo,pause,
         hee,wheet,pause,
         wheeo,hee,wheet,pause
         ]
      )
      prob = heidi2tita2(from,A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      if results.count == 1 {
         XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: to), "Result is false")
      }
   }

   // Test Tita -> Heidi
   func testTita2Heidi2() {
      let A = Variable(named: "A")

      var from = toTita([wheet,hee,wheet,pause,wheeo,hee,wheet,pause,wheeo,wheet,pause])
      var to = toHeidi([davent,deponer,returnar])
      var prob = tita2heidi2(from,A)
      var results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      if results.count == 1 {
         XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: to), "Result is false")
      }

      from = toTita([wheet,wheeo,wheeo,pause,wheet,wheeo,wheeo,pause])
      to = toHeidi([plaun,plaun])
      prob = tita2heidi2(from,A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      if results.count == 1 {
         XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: to), "Result is false")
      }

      from = toTita(
         [
         wheeo,wheeo,pause,
         wheeo,wheet,pause,
         wheet,wheeo,wheeo,pause,
         wheet,wheeo,wheet,pause,
         wheet,hee,wheet,pause,
         wheet,wheeo,pause,
         hee,wheet,pause,
         wheeo,hee,wheet,pause
         ]
      )
      to = toHeidi([sa_fermar,returnar,plaun,davos,davent,sanester,dretg,deponer])
      prob = tita2heidi2(from,A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      if results.count == 1 {
         XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: to), "Result is false")
      }
   }

   // Proof required that Heidi -> Tita -> Heidi gives back the original order
   func proof() {

      var order: Term
      var res: [[Variable: Wrapper]]
      let I = Variable(named: "I")
      let R = Variable(named: "R")

      // For all 8 romansh orders
      for ord in [deponer,dretg,sanester,davent,davos,plaun,returnar,sa_fermar] {

         order = List.cons(ord,List.empty)

         // Find the "whistle equivalent"
         for sol in solve(heidi2tita2(order,I)) {

            // Go back to romansh
            res = resultsOf(goal: tita2heidi2(sol[I], R), variables: [R])

            // Then check if it is back to the original
            XCTAssertEqual(res.count, 1, "Number of results is wrong")
            if res.count == 1 {
               XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(res)[0][R]!, Wrapper(term: order), "Result is false")
            }
         }
      }
      /* We've proven that any sequence of 1 order will be correct.
       * By recurrence, we suppose that any sequence of n orders will be correct
       * and it follows that, with a sequence of n+1 orders, since we can
       * guarantee that it will be correct up to the nth element without
       * ambiguity, all that will be left is 1 order (the last) that, as already
       * proven (since the sequences are unambiguously delimited), will be
       * evaluated correctly. CQFD
       */
   }


//==============================================================================
// Semantic 3 tests
//==============================================================================

   // Test for the 3rd semantics (spoiler: it is flawed)
   func testAcceleratedSemantic() {

      let T = Variable(named: "T")
      let H = Variable(named: "H")
      var counter = 1

      let orders = toHeidi([plaun,dretg,plaun,deponer,sa_fermar])

      // Get all translations heidi -> tita for the sequence given, then all the
      // translations tita -> heidi for each previous solution.
      for sol1 in solve(heidi2tita3(orders, T)) {
         for sol2 in solve(tita2heidi3(sol1[T], H)) {
            print("\(counter)) ", terminator: "")
            print(sol2.reified()[H])
            counter += 1
         }
      }

      // There are 4 solutions, 3 of which are incorrect, because of the lack of
      // separation between the orders.
   }

   // Collect all possible problems
   func allProblems() {

      print("\nGeneral form: original order(s) -> overlapping order")

      let R = Variable(named: "R")
      var res: [[Variable: Wrapper]]
      var i = 0

      // Define all romansh orders in whistle
      let deponerw   = [wheeo,whee,wheet]
      let dretgw     = [hee,wheet]
      let sanesterw  = [wheet,wheeo]
      let daventw    = [wheet,hee,wheet]
      let davosw     = [wheet,wheeo,wheet]
      let plaunw     = [wheet,wheeo,wheeo]
      let returnarw  = [wheeo,wheet]
      let sa_fermarw = [wheeo,wheeo]

      // A problem can arise if a 3-whistle order "contains" a 2-whistle one.
      // We know that there is no risk of same-length orders to overlap (by
      // their definition).

      print("\nList of problematic singletons:")

      // For all 3-whistle romansh orders
      let whistle3 = [deponer,davent,davos,plaun]
      for ord in [deponerw,daventw,davosw,plaunw] {

         // 2 possible "wrong" sectioning
         res = resultsOf(goal: tita2heidi3(toTita(Array(ord[0...1])), R), variables: [R])
         if (res.count > 0) {
            print("\(whistle3[i])\t-> \((res[0][R])!.description)")
         }
         res = resultsOf(goal: tita2heidi3(toTita(Array(ord[1...2])), R), variables: [R])
         if (res.count > 0) {
            print("\(whistle3[i])\t-> \((res[0][R])!.description)")
         }

         i += 1
      }

      // Given the length of the sequences, the only other type of problem that
      // can appear is when there is an order overlapping a sequence of 2 orders.

      print("\nList of problematic couples:")

      var order: [Term]
      var end: Int
      i = 0
      var j = 0

      // For all couple of orders
      let whistles = [deponer,dretg,sanester,davent,davos,plaun,returnar,sa_fermar]
      for ord1 in [deponerw,dretgw,sanesterw,daventw,davosw,plaunw,returnarw,sa_fermarw] {
         for ord2 in [deponerw,dretgw,sanesterw,daventw,davosw,plaunw,returnarw,sa_fermarw] {

            // Get the size 2 overlap
            order = [ord1.last!, ord2[0]]
            res = resultsOf(goal: tita2heidi3(toTita(order), R), variables: [R])
            if (res.count > 0) {
               print(
                  "\([whistles[i],whistles[j]])".padding(
                     toLength: 24, withPad: " ", startingAt: 0
                  ) + "-> \((res[0][R])!.description)"
               )
            }

            // Get the first size 3 overlap
            end = ord1.endIndex-1
            order = [ord1[end-1], ord1[end], ord2[0]]
            res = resultsOf(goal: tita2heidi3(toTita(order), R), variables: [R])
            if (res.count > 0) {
               print(
                  "\([whistles[i],whistles[j]])".padding(
                     toLength: 24, withPad: " ", startingAt: 0
                  ) + "-> \((res[0][R])!.description)"
               )
            }

            // Get the second size 3 overlap
            order = [ord1.last!, ord2[0], ord2[1]]
            res = resultsOf(goal: tita2heidi3(toTita(order), R), variables: [R])
            if (res.count > 0) {
               print(
                  "\([whistles[i],whistles[j]])".padding(
                     toLength: 24, withPad: " ", startingAt: 0
                  ) + "-> \((res[0][R])!.description)"
               )
            }

            j += 1
         }
         i += 1
         j = 0
      }
      print("")
   }


   // Display for readability
   func endTests() {
      print("\n[End of tests]\n")
   }

   static var allTests : [(String, (heidiTests) -> () throws -> Void)] {
      return [
         ("startTests", startTests),
         ("testHeidiSeq", testHeidiSeq),
         ("testTitaSeq", testTitaSeq),
         ("testHeidi2Tita1", testHeidi2Tita1),
         ("testTita2Heidi1", testTita2Heidi1),
         ("testHeidi2Tita2", testHeidi2Tita2),
         ("testTita2Heidi2", testTita2Heidi2),
         ("proof", proof),
         ("testAcceleratedSemantic", testAcceleratedSemantic),
         ("allProblems", allProblems),
         ("endTests", endTests),
      ]
   }

}
