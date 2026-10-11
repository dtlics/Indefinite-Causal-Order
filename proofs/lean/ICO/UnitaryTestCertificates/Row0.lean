import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_0 : ∀ i : Fin 128,
    testRow 0 i.val = (2*(gaussianEntry 0 i.val).1, 2*(gaussianEntry 0 i.val).2) := by
  decide +kernel
theorem ann_zero_0 : ∀ b : Fin 4, annihilation 0 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_0 : 0 < qNorm (uData 0) ∧ 0 < qNorm (vData 0) := by
  decide +kernel
end ICO.UnitaryTestCertificates
