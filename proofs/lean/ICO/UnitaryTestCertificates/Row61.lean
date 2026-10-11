import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_61 : ∀ i : Fin 128,
    testRow 61 i.val = (2*(gaussianEntry 61 i.val).1, 2*(gaussianEntry 61 i.val).2) := by
  decide +kernel
theorem ann_zero_61 : ∀ b : Fin 4, annihilation 61 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_61 : 0 < qNorm (uData 61) ∧ 0 < qNorm (vData 61) := by
  decide +kernel
end ICO.UnitaryTestCertificates
