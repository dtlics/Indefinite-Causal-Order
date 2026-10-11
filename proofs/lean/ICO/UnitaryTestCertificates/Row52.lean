import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_52 : ∀ i : Fin 128,
    testRow 52 i.val = (2*(gaussianEntry 52 i.val).1, 2*(gaussianEntry 52 i.val).2) := by
  decide +kernel
theorem ann_zero_52 : ∀ b : Fin 4, annihilation 52 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_52 : 0 < qNorm (uData 52) ∧ 0 < qNorm (vData 52) := by
  decide +kernel
end ICO.UnitaryTestCertificates
