import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_48 : ∀ i : Fin 128,
    testRow 48 i.val = (2*(gaussianEntry 48 i.val).1, 2*(gaussianEntry 48 i.val).2) := by
  decide +kernel
theorem ann_zero_48 : ∀ b : Fin 4, annihilation 48 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_48 : 0 < qNorm (uData 48) ∧ 0 < qNorm (vData 48) := by
  decide +kernel
end ICO.UnitaryTestCertificates
