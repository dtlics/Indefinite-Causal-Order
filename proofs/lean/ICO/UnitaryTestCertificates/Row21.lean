import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_21 : ∀ i : Fin 128,
    testRow 21 i.val = (2*(gaussianEntry 21 i.val).1, 2*(gaussianEntry 21 i.val).2) := by
  decide +kernel
theorem ann_zero_21 : ∀ b : Fin 4, annihilation 21 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_21 : 0 < qNorm (uData 21) ∧ 0 < qNorm (vData 21) := by
  decide +kernel
end ICO.UnitaryTestCertificates
