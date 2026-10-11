import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_11 : ∀ i : Fin 128,
    testRow 11 i.val = (2*(gaussianEntry 11 i.val).1, 2*(gaussianEntry 11 i.val).2) := by
  decide +kernel
theorem ann_zero_11 : ∀ b : Fin 4, annihilation 11 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_11 : 0 < qNorm (uData 11) ∧ 0 < qNorm (vData 11) := by
  decide +kernel
end ICO.UnitaryTestCertificates
