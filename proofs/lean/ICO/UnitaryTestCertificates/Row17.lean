import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_17 : ∀ i : Fin 128,
    testRow 17 i.val = (2*(gaussianEntry 17 i.val).1, 2*(gaussianEntry 17 i.val).2) := by
  decide +kernel
theorem ann_zero_17 : ∀ b : Fin 4, annihilation 17 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_17 : 0 < qNorm (uData 17) ∧ 0 < qNorm (vData 17) := by
  decide +kernel
end ICO.UnitaryTestCertificates
