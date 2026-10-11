import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_53 : ∀ i : Fin 128,
    testRow 53 i.val = (2*(gaussianEntry 53 i.val).1, 2*(gaussianEntry 53 i.val).2) := by
  decide +kernel
theorem ann_zero_53 : ∀ b : Fin 4, annihilation 53 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_53 : 0 < qNorm (uData 53) ∧ 0 < qNorm (vData 53) := by
  decide +kernel
end ICO.UnitaryTestCertificates
