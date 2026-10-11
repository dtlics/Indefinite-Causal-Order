import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_24 : ∀ i : Fin 128,
    testRow 24 i.val = (2*(gaussianEntry 24 i.val).1, 2*(gaussianEntry 24 i.val).2) := by
  decide +kernel
theorem ann_zero_24 : ∀ b : Fin 4, annihilation 24 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_24 : 0 < qNorm (uData 24) ∧ 0 < qNorm (vData 24) := by
  decide +kernel
end ICO.UnitaryTestCertificates
