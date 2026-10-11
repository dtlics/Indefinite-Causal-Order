import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_42 : ∀ i : Fin 128,
    testRow 42 i.val = (2*(gaussianEntry 42 i.val).1, 2*(gaussianEntry 42 i.val).2) := by
  decide +kernel
theorem ann_zero_42 : ∀ b : Fin 4, annihilation 42 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_42 : 0 < qNorm (uData 42) ∧ 0 < qNorm (vData 42) := by
  decide +kernel
end ICO.UnitaryTestCertificates
