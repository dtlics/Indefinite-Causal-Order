import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_3 : ∀ i : Fin 128,
    testRow 3 i.val = (2*(gaussianEntry 3 i.val).1, 2*(gaussianEntry 3 i.val).2) := by
  decide +kernel
theorem ann_zero_3 : ∀ b : Fin 4, annihilation 3 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_3 : 0 < qNorm (uData 3) ∧ 0 < qNorm (vData 3) := by
  decide +kernel
end ICO.UnitaryTestCertificates
