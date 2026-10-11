import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_75 : ∀ i : Fin 128,
    testRow 75 i.val = (2*(gaussianEntry 75 i.val).1, 2*(gaussianEntry 75 i.val).2) := by
  decide +kernel
theorem ann_zero_75 : ∀ b : Fin 4, annihilation 75 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_75 : 0 < qNorm (uData 75) ∧ 0 < qNorm (vData 75) := by
  decide +kernel
end ICO.UnitaryTestCertificates
