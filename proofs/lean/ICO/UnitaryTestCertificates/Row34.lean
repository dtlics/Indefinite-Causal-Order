import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_34 : ∀ i : Fin 128,
    testRow 34 i.val = (2*(gaussianEntry 34 i.val).1, 2*(gaussianEntry 34 i.val).2) := by
  decide +kernel
theorem ann_zero_34 : ∀ b : Fin 4, annihilation 34 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_34 : 0 < qNorm (uData 34) ∧ 0 < qNorm (vData 34) := by
  decide +kernel
end ICO.UnitaryTestCertificates
