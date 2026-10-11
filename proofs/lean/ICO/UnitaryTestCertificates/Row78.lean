import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_78 : ∀ i : Fin 128,
    testRow 78 i.val = (2*(gaussianEntry 78 i.val).1, 2*(gaussianEntry 78 i.val).2) := by
  decide +kernel
theorem ann_zero_78 : ∀ b : Fin 4, annihilation 78 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_78 : 0 < qNorm (uData 78) ∧ 0 < qNorm (vData 78) := by
  decide +kernel
end ICO.UnitaryTestCertificates
