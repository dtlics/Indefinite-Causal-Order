import ICO.SupportBasisProducts.Row105
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_105 (b : Fin 25) :
    basisProductRe 105 b.val = (if 105 = 103+b.val then 1 else 0) ∧
    basisProductIm 105 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_105_0, basis_im_105_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_105_1, basis_im_105_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_105_2, basis_im_105_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_105_3, basis_im_105_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_105_4, basis_im_105_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_105_5, basis_im_105_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_105_6, basis_im_105_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_105_7, basis_im_105_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_105_8, basis_im_105_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_105_9, basis_im_105_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_105_10, basis_im_105_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_105_11, basis_im_105_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_105_12, basis_im_105_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_105_13, basis_im_105_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_105_14, basis_im_105_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_105_15, basis_im_105_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_105_16, basis_im_105_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_105_17, basis_im_105_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_105_18, basis_im_105_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_105_19, basis_im_105_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_105_20, basis_im_105_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_105_21, basis_im_105_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_105_22, basis_im_105_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_105_23, basis_im_105_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_105_24, basis_im_105_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
