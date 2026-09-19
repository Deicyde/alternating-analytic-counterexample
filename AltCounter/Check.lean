/-
Axiom check: the build fails if any of the main results depends on anything other than the three standard axioms.
-/
import AltCounter.MainNSC

/-- info: 'AltCounter.not_analyticAt_Q_of_NSC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AltCounter.not_analyticAt_Q_of_NSC

/-- info: 'AltCounter.not_contDiff_omega_Q_of_NSC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AltCounter.not_contDiff_omega_Q_of_NSC

/-- info: 'AltCounter.not_analyticAt_Q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AltCounter.not_analyticAt_Q

/-- info: 'AltCounter.not_contDiff_omega_Q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AltCounter.not_contDiff_omega_Q

/-- info: 'AltCounter.tailProperty_of_NSC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AltCounter.tailProperty_of_NSC

/-- info: 'AltCounter.core_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AltCounter.core_false

/-- info: 'AltCounter.exists_block_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AltCounter.exists_block_point

/-- info: 'AltCounter.exists_bilinear_of_analyticAt_of_homogeneous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AltCounter.exists_bilinear_of_analyticAt_of_homogeneous

