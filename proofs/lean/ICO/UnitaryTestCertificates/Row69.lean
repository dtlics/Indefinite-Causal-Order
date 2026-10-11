import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_69 : ∀ i : Fin 128,
    testRow 69 i.val = (2*(gaussianEntry 69 i.val).1, 2*(gaussianEntry 69 i.val).2) := by
  decide +kernel
theorem ann_zero_69 : ∀ b : Fin 4, annihilation 69 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_69 : 0 < qNorm (uData 69) ∧ 0 < qNorm (vData 69) := by
  decide +kernel
end ICO.UnitaryTestCertificates
