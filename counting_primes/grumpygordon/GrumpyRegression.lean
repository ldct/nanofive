import GrumpyGordon

/-! Check intermediate states too: final counts alone will not catch replacing
this algorithm by a different prime counter. -/
open TinyFive.GrumpyGordon

private def start := init 1000 31
private def after3 := step 1000 31 3 start
private def after5 := step 1000 31 5 after3

#guard start.pc == 0 && start.larges[0]! == 499
#guard after3.pc == 1 && after3.roughs == [5,7,11,13,17,19,23,25,29,31]
#guard after5.pc == 2 && after5.roughs == [7,11,13,17,19,23,29,31]
#guard after5.larges == #[267,39,25,21,16,15,13,10,10]
#guard large after5 11 == 25 && small after5 25 == small after5 24
-- For q = 11 the smaller factor 7 accounts for 7*7*11 and 7*11*11.
#guard triples (small after5) after5.roughs 11 (1000/11) == 2
#guard finish 1000 31 (small after5) (large after5) after5.roughs == 168
