import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_39 : ∀ i : Fin 128,
    testRow 39 i.val = (2*(gaussianEntry 39 i.val).1, 2*(gaussianEntry 39 i.val).2) := by
  decide +kernel
theorem ann_zero_39 : ∀ b : Fin 4, annihilation 39 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_39 : 0 < qNorm (uData 39) ∧ 0 < qNorm (vData 39) := by
  decide +kernel
end ICO.UnitaryTestCertificates
