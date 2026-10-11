import ICO.SupportBasisProducts.Row14
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_14 (b : Fin 25) :
    basisProductRe 14 b.val = (if 14 = 103+b.val then 1 else 0) ∧
    basisProductIm 14 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_14_0, basis_im_14_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_14_1, basis_im_14_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_14_2, basis_im_14_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_14_3, basis_im_14_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_14_4, basis_im_14_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_14_5, basis_im_14_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_14_6, basis_im_14_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_14_7, basis_im_14_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_14_8, basis_im_14_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_14_9, basis_im_14_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_14_10, basis_im_14_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_14_11, basis_im_14_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_14_12, basis_im_14_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_14_13, basis_im_14_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_14_14, basis_im_14_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_14_15, basis_im_14_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_14_16, basis_im_14_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_14_17, basis_im_14_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_14_18, basis_im_14_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_14_19, basis_im_14_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_14_20, basis_im_14_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_14_21, basis_im_14_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_14_22, basis_im_14_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_14_23, basis_im_14_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_14_24, basis_im_14_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
