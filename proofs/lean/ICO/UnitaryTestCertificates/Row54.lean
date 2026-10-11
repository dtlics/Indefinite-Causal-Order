import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_54 : ∀ i : Fin 128,
    testRow 54 i.val = (2*(gaussianEntry 54 i.val).1, 2*(gaussianEntry 54 i.val).2) := by
  decide +kernel
theorem ann_zero_54 : ∀ b : Fin 4, annihilation 54 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_54 : 0 < qNorm (uData 54) ∧ 0 < qNorm (vData 54) := by
  decide +kernel
end ICO.UnitaryTestCertificates
