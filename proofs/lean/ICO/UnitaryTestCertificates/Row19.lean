import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_19 : ∀ i : Fin 128,
    testRow 19 i.val = (2*(gaussianEntry 19 i.val).1, 2*(gaussianEntry 19 i.val).2) := by
  decide +kernel
theorem ann_zero_19 : ∀ b : Fin 4, annihilation 19 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_19 : 0 < qNorm (uData 19) ∧ 0 < qNorm (vData 19) := by
  decide +kernel
end ICO.UnitaryTestCertificates
