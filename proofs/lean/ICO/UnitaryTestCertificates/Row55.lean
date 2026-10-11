import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_55 : ∀ i : Fin 128,
    testRow 55 i.val = (2*(gaussianEntry 55 i.val).1, 2*(gaussianEntry 55 i.val).2) := by
  decide +kernel
theorem ann_zero_55 : ∀ b : Fin 4, annihilation 55 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_55 : 0 < qNorm (uData 55) ∧ 0 < qNorm (vData 55) := by
  decide +kernel
end ICO.UnitaryTestCertificates
