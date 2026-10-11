import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_30 : ∀ i : Fin 128,
    testRow 30 i.val = (2*(gaussianEntry 30 i.val).1, 2*(gaussianEntry 30 i.val).2) := by
  decide +kernel
theorem ann_zero_30 : ∀ b : Fin 4, annihilation 30 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_30 : 0 < qNorm (uData 30) ∧ 0 < qNorm (vData 30) := by
  decide +kernel
end ICO.UnitaryTestCertificates
