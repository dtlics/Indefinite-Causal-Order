import ICO.SupportBasisProducts.Row31
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_31 (b : Fin 25) :
    basisProductRe 31 b.val = (if 31 = 103+b.val then 1 else 0) ∧
    basisProductIm 31 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_31_0, basis_im_31_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_31_1, basis_im_31_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_31_2, basis_im_31_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_31_3, basis_im_31_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_31_4, basis_im_31_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_31_5, basis_im_31_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_31_6, basis_im_31_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_31_7, basis_im_31_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_31_8, basis_im_31_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_31_9, basis_im_31_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_31_10, basis_im_31_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_31_11, basis_im_31_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_31_12, basis_im_31_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_31_13, basis_im_31_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_31_14, basis_im_31_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_31_15, basis_im_31_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_31_16, basis_im_31_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_31_17, basis_im_31_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_31_18, basis_im_31_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_31_19, basis_im_31_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_31_20, basis_im_31_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_31_21, basis_im_31_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_31_22, basis_im_31_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_31_23, basis_im_31_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_31_24, basis_im_31_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
