import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_37 : ∀ i : Fin 128,
    testRow 37 i.val = (2*(gaussianEntry 37 i.val).1, 2*(gaussianEntry 37 i.val).2) := by
  decide +kernel
theorem ann_zero_37 : ∀ b : Fin 4, annihilation 37 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_37 : 0 < qNorm (uData 37) ∧ 0 < qNorm (vData 37) := by
  decide +kernel
end ICO.UnitaryTestCertificates
