import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_2 : ∀ i : Fin 128,
    testRow 2 i.val = (2*(gaussianEntry 2 i.val).1, 2*(gaussianEntry 2 i.val).2) := by
  decide +kernel
theorem ann_zero_2 : ∀ b : Fin 4, annihilation 2 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_2 : 0 < qNorm (uData 2) ∧ 0 < qNorm (vData 2) := by
  decide +kernel
end ICO.UnitaryTestCertificates
