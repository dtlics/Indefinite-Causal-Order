import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_72 : ∀ i : Fin 128,
    testRow 72 i.val = (2*(gaussianEntry 72 i.val).1, 2*(gaussianEntry 72 i.val).2) := by
  decide +kernel
theorem ann_zero_72 : ∀ b : Fin 4, annihilation 72 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_72 : 0 < qNorm (uData 72) ∧ 0 < qNorm (vData 72) := by
  decide +kernel
end ICO.UnitaryTestCertificates
