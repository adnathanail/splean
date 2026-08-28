import LSpec
import SpLean.Algebraic.AlgPhase

namespace Tests.Algebraic.AlgPhase

open LSpec

private def zero : _root_.AlgPhase := 0
private def pi : _root_.AlgPhase := 1
private def twoPi : _root_.AlgPhase := 2
private def piOverTwo : _root_.AlgPhase := (1 / 2)
private def minusPi : _root_.AlgPhase := -1
private def minusPiOverTwo : _root_.AlgPhase := -(1 / 2)
private def threePi : _root_.AlgPhase := 3

private def formatTests : TestSeq :=
  group "format" $
    test "zero" (zero.format = "0") $
    test "pi" (pi.format = "π") $
    test "two pi" (twoPi.format = "2π") $
    test "pi over two" (piOverTwo.format = "π/2") $
    test "minus pi" (minusPi.format = "-π") $
    test "minus pi over two" (minusPiOverTwo.format = "-π/2")

def tests : TestSeq :=
  group "AlgPhase" $
    formatTests

end Tests.Algebraic.AlgPhase
