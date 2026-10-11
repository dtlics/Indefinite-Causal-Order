import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_91 : ∀ i : Fin 128,
    testRow 91 i.val = (2*(gaussianEntry 91 i.val).1, 2*(gaussianEntry 91 i.val).2) := by
  decide +kernel
theorem ann_zero_91 : ∀ b : Fin 4, annihilation 91 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_91 : 0 < qNorm (uData 91) ∧ 0 < qNorm (vData 91) := by
  decide +kernel
end ICO.UnitaryTestCertificates
