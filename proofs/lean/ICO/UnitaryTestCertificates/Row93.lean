import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_93 : ∀ i : Fin 128,
    testRow 93 i.val = (2*(gaussianEntry 93 i.val).1, 2*(gaussianEntry 93 i.val).2) := by
  decide +kernel
theorem ann_zero_93 : ∀ b : Fin 4, annihilation 93 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_93 : 0 < qNorm (uData 93) ∧ 0 < qNorm (vData 93) := by
  decide +kernel
end ICO.UnitaryTestCertificates
