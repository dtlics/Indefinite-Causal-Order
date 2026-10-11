import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_73 : ∀ i : Fin 128,
    testRow 73 i.val = (2*(gaussianEntry 73 i.val).1, 2*(gaussianEntry 73 i.val).2) := by
  decide +kernel
theorem ann_zero_73 : ∀ b : Fin 4, annihilation 73 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_73 : 0 < qNorm (uData 73) ∧ 0 < qNorm (vData 73) := by
  decide +kernel
end ICO.UnitaryTestCertificates
