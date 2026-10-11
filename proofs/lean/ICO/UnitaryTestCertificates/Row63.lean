import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_63 : ∀ i : Fin 128,
    testRow 63 i.val = (2*(gaussianEntry 63 i.val).1, 2*(gaussianEntry 63 i.val).2) := by
  decide +kernel
theorem ann_zero_63 : ∀ b : Fin 4, annihilation 63 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_63 : 0 < qNorm (uData 63) ∧ 0 < qNorm (vData 63) := by
  decide +kernel
end ICO.UnitaryTestCertificates
