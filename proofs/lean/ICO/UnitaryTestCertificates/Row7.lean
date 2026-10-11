import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_7 : ∀ i : Fin 128,
    testRow 7 i.val = (2*(gaussianEntry 7 i.val).1, 2*(gaussianEntry 7 i.val).2) := by
  decide +kernel
theorem ann_zero_7 : ∀ b : Fin 4, annihilation 7 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_7 : 0 < qNorm (uData 7) ∧ 0 < qNorm (vData 7) := by
  decide +kernel
end ICO.UnitaryTestCertificates
