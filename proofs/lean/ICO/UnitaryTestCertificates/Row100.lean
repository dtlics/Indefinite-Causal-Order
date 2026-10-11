import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_100 : ∀ i : Fin 128,
    testRow 100 i.val = (2*(gaussianEntry 100 i.val).1, 2*(gaussianEntry 100 i.val).2) := by
  decide +kernel
theorem ann_zero_100 : ∀ b : Fin 4, annihilation 100 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_100 : 0 < qNorm (uData 100) ∧ 0 < qNorm (vData 100) := by
  decide +kernel
end ICO.UnitaryTestCertificates
