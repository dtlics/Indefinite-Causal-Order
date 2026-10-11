import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_50 : ∀ i : Fin 128,
    testRow 50 i.val = (2*(gaussianEntry 50 i.val).1, 2*(gaussianEntry 50 i.val).2) := by
  decide +kernel
theorem ann_zero_50 : ∀ b : Fin 4, annihilation 50 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_50 : 0 < qNorm (uData 50) ∧ 0 < qNorm (vData 50) := by
  decide +kernel
end ICO.UnitaryTestCertificates
