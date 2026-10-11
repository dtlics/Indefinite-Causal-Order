import ICO.SupportBasisProducts.Row36
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_36 (b : Fin 25) :
    basisProductRe 36 b.val = (if 36 = 103+b.val then 1 else 0) ∧
    basisProductIm 36 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_36_0, basis_im_36_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_36_1, basis_im_36_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_36_2, basis_im_36_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_36_3, basis_im_36_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_36_4, basis_im_36_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_36_5, basis_im_36_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_36_6, basis_im_36_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_36_7, basis_im_36_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_36_8, basis_im_36_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_36_9, basis_im_36_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_36_10, basis_im_36_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_36_11, basis_im_36_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_36_12, basis_im_36_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_36_13, basis_im_36_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_36_14, basis_im_36_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_36_15, basis_im_36_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_36_16, basis_im_36_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_36_17, basis_im_36_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_36_18, basis_im_36_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_36_19, basis_im_36_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_36_20, basis_im_36_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_36_21, basis_im_36_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_36_22, basis_im_36_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_36_23, basis_im_36_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_36_24, basis_im_36_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
