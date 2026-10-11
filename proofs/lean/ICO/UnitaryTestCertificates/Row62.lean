import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_62 : ∀ i : Fin 128,
    testRow 62 i.val = (2*(gaussianEntry 62 i.val).1, 2*(gaussianEntry 62 i.val).2) := by
  decide +kernel
theorem ann_zero_62 : ∀ b : Fin 4, annihilation 62 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_62 : 0 < qNorm (uData 62) ∧ 0 < qNorm (vData 62) := by
  decide +kernel
end ICO.UnitaryTestCertificates
