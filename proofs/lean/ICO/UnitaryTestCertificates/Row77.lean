import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_77 : ∀ i : Fin 128,
    testRow 77 i.val = (2*(gaussianEntry 77 i.val).1, 2*(gaussianEntry 77 i.val).2) := by
  decide +kernel
theorem ann_zero_77 : ∀ b : Fin 4, annihilation 77 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_77 : 0 < qNorm (uData 77) ∧ 0 < qNorm (vData 77) := by
  decide +kernel
end ICO.UnitaryTestCertificates
