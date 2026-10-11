import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_57 : ∀ i : Fin 128,
    testRow 57 i.val = (2*(gaussianEntry 57 i.val).1, 2*(gaussianEntry 57 i.val).2) := by
  decide +kernel
theorem ann_zero_57 : ∀ b : Fin 4, annihilation 57 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_57 : 0 < qNorm (uData 57) ∧ 0 < qNorm (vData 57) := by
  decide +kernel
end ICO.UnitaryTestCertificates
