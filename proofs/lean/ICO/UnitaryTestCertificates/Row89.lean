import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_89 : ∀ i : Fin 128,
    testRow 89 i.val = (2*(gaussianEntry 89 i.val).1, 2*(gaussianEntry 89 i.val).2) := by
  decide +kernel
theorem ann_zero_89 : ∀ b : Fin 4, annihilation 89 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_89 : 0 < qNorm (uData 89) ∧ 0 < qNorm (vData 89) := by
  decide +kernel
end ICO.UnitaryTestCertificates
