import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_43 : ∀ i : Fin 128,
    testRow 43 i.val = (2*(gaussianEntry 43 i.val).1, 2*(gaussianEntry 43 i.val).2) := by
  decide +kernel
theorem ann_zero_43 : ∀ b : Fin 4, annihilation 43 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_43 : 0 < qNorm (uData 43) ∧ 0 < qNorm (vData 43) := by
  decide +kernel
end ICO.UnitaryTestCertificates
