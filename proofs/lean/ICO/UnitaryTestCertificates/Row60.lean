import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_60 : ∀ i : Fin 128,
    testRow 60 i.val = (2*(gaussianEntry 60 i.val).1, 2*(gaussianEntry 60 i.val).2) := by
  decide +kernel
theorem ann_zero_60 : ∀ b : Fin 4, annihilation 60 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_60 : 0 < qNorm (uData 60) ∧ 0 < qNorm (vData 60) := by
  decide +kernel
end ICO.UnitaryTestCertificates
