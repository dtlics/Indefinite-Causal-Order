import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_66 : ∀ i : Fin 128,
    testRow 66 i.val = (2*(gaussianEntry 66 i.val).1, 2*(gaussianEntry 66 i.val).2) := by
  decide +kernel
theorem ann_zero_66 : ∀ b : Fin 4, annihilation 66 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_66 : 0 < qNorm (uData 66) ∧ 0 < qNorm (vData 66) := by
  decide +kernel
end ICO.UnitaryTestCertificates
