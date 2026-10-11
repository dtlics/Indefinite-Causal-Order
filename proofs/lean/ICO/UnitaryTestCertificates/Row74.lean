import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_74 : ∀ i : Fin 128,
    testRow 74 i.val = (2*(gaussianEntry 74 i.val).1, 2*(gaussianEntry 74 i.val).2) := by
  decide +kernel
theorem ann_zero_74 : ∀ b : Fin 4, annihilation 74 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_74 : 0 < qNorm (uData 74) ∧ 0 < qNorm (vData 74) := by
  decide +kernel
end ICO.UnitaryTestCertificates
