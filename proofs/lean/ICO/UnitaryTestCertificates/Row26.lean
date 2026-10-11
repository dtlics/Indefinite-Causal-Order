import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_26 : ∀ i : Fin 128,
    testRow 26 i.val = (2*(gaussianEntry 26 i.val).1, 2*(gaussianEntry 26 i.val).2) := by
  decide +kernel
theorem ann_zero_26 : ∀ b : Fin 4, annihilation 26 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_26 : 0 < qNorm (uData 26) ∧ 0 < qNorm (vData 26) := by
  decide +kernel
end ICO.UnitaryTestCertificates
