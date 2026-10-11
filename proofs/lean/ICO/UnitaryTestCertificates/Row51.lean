import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_51 : ∀ i : Fin 128,
    testRow 51 i.val = (2*(gaussianEntry 51 i.val).1, 2*(gaussianEntry 51 i.val).2) := by
  decide +kernel
theorem ann_zero_51 : ∀ b : Fin 4, annihilation 51 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_51 : 0 < qNorm (uData 51) ∧ 0 < qNorm (vData 51) := by
  decide +kernel
end ICO.UnitaryTestCertificates
