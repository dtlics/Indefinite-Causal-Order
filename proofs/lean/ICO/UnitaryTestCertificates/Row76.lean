import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_76 : ∀ i : Fin 128,
    testRow 76 i.val = (2*(gaussianEntry 76 i.val).1, 2*(gaussianEntry 76 i.val).2) := by
  decide +kernel
theorem ann_zero_76 : ∀ b : Fin 4, annihilation 76 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_76 : 0 < qNorm (uData 76) ∧ 0 < qNorm (vData 76) := by
  decide +kernel
end ICO.UnitaryTestCertificates
