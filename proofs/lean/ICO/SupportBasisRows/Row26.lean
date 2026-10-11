import ICO.SupportBasisProducts.Row26
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_26 (b : Fin 25) :
    basisProductRe 26 b.val = (if 26 = 103+b.val then 1 else 0) ∧
    basisProductIm 26 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_26_0, basis_im_26_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_26_1, basis_im_26_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_26_2, basis_im_26_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_26_3, basis_im_26_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_26_4, basis_im_26_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_26_5, basis_im_26_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_26_6, basis_im_26_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_26_7, basis_im_26_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_26_8, basis_im_26_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_26_9, basis_im_26_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_26_10, basis_im_26_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_26_11, basis_im_26_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_26_12, basis_im_26_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_26_13, basis_im_26_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_26_14, basis_im_26_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_26_15, basis_im_26_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_26_16, basis_im_26_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_26_17, basis_im_26_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_26_18, basis_im_26_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_26_19, basis_im_26_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_26_20, basis_im_26_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_26_21, basis_im_26_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_26_22, basis_im_26_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_26_23, basis_im_26_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_26_24, basis_im_26_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
