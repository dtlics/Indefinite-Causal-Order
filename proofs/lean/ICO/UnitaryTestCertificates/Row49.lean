import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_49 : ∀ i : Fin 128,
    testRow 49 i.val = (2*(gaussianEntry 49 i.val).1, 2*(gaussianEntry 49 i.val).2) := by
  decide +kernel
theorem ann_zero_49 : ∀ b : Fin 4, annihilation 49 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_49 : 0 < qNorm (uData 49) ∧ 0 < qNorm (vData 49) := by
  decide +kernel
end ICO.UnitaryTestCertificates
