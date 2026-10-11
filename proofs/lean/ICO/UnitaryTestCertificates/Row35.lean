import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_35 : ∀ i : Fin 128,
    testRow 35 i.val = (2*(gaussianEntry 35 i.val).1, 2*(gaussianEntry 35 i.val).2) := by
  decide +kernel
theorem ann_zero_35 : ∀ b : Fin 4, annihilation 35 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_35 : 0 < qNorm (uData 35) ∧ 0 < qNorm (vData 35) := by
  decide +kernel
end ICO.UnitaryTestCertificates
