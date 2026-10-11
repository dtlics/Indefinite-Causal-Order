import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_82 : ∀ i : Fin 128,
    testRow 82 i.val = (2*(gaussianEntry 82 i.val).1, 2*(gaussianEntry 82 i.val).2) := by
  decide +kernel
theorem ann_zero_82 : ∀ b : Fin 4, annihilation 82 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_82 : 0 < qNorm (uData 82) ∧ 0 < qNorm (vData 82) := by
  decide +kernel
end ICO.UnitaryTestCertificates
