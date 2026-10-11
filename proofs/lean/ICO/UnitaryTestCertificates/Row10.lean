import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_10 : ∀ i : Fin 128,
    testRow 10 i.val = (2*(gaussianEntry 10 i.val).1, 2*(gaussianEntry 10 i.val).2) := by
  decide +kernel
theorem ann_zero_10 : ∀ b : Fin 4, annihilation 10 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_10 : 0 < qNorm (uData 10) ∧ 0 < qNorm (vData 10) := by
  decide +kernel
end ICO.UnitaryTestCertificates
