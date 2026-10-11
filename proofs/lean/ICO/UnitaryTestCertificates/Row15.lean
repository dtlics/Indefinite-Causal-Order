import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_15 : ∀ i : Fin 128,
    testRow 15 i.val = (2*(gaussianEntry 15 i.val).1, 2*(gaussianEntry 15 i.val).2) := by
  decide +kernel
theorem ann_zero_15 : ∀ b : Fin 4, annihilation 15 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_15 : 0 < qNorm (uData 15) ∧ 0 < qNorm (vData 15) := by
  decide +kernel
end ICO.UnitaryTestCertificates
