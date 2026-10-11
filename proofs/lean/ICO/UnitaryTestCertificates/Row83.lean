import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_83 : ∀ i : Fin 128,
    testRow 83 i.val = (2*(gaussianEntry 83 i.val).1, 2*(gaussianEntry 83 i.val).2) := by
  decide +kernel
theorem ann_zero_83 : ∀ b : Fin 4, annihilation 83 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_83 : 0 < qNorm (uData 83) ∧ 0 < qNorm (vData 83) := by
  decide +kernel
end ICO.UnitaryTestCertificates
