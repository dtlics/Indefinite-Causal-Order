import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_20 : ∀ i : Fin 128,
    testRow 20 i.val = (2*(gaussianEntry 20 i.val).1, 2*(gaussianEntry 20 i.val).2) := by
  decide +kernel
theorem ann_zero_20 : ∀ b : Fin 4, annihilation 20 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_20 : 0 < qNorm (uData 20) ∧ 0 < qNorm (vData 20) := by
  decide +kernel
end ICO.UnitaryTestCertificates
