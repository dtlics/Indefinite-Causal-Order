import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_38 : ∀ i : Fin 128,
    testRow 38 i.val = (2*(gaussianEntry 38 i.val).1, 2*(gaussianEntry 38 i.val).2) := by
  decide +kernel
theorem ann_zero_38 : ∀ b : Fin 4, annihilation 38 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_38 : 0 < qNorm (uData 38) ∧ 0 < qNorm (vData 38) := by
  decide +kernel
end ICO.UnitaryTestCertificates
