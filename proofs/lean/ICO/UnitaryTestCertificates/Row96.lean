import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_96 : ∀ i : Fin 128,
    testRow 96 i.val = (2*(gaussianEntry 96 i.val).1, 2*(gaussianEntry 96 i.val).2) := by
  decide +kernel
theorem ann_zero_96 : ∀ b : Fin 4, annihilation 96 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_96 : 0 < qNorm (uData 96) ∧ 0 < qNorm (vData 96) := by
  decide +kernel
end ICO.UnitaryTestCertificates
