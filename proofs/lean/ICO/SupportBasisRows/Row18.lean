import ICO.SupportBasisProducts.Row18
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_18 (b : Fin 25) :
    basisProductRe 18 b.val = (if 18 = 103+b.val then 1 else 0) ∧
    basisProductIm 18 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_18_0, basis_im_18_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_18_1, basis_im_18_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_18_2, basis_im_18_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_18_3, basis_im_18_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_18_4, basis_im_18_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_18_5, basis_im_18_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_18_6, basis_im_18_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_18_7, basis_im_18_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_18_8, basis_im_18_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_18_9, basis_im_18_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_18_10, basis_im_18_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_18_11, basis_im_18_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_18_12, basis_im_18_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_18_13, basis_im_18_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_18_14, basis_im_18_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_18_15, basis_im_18_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_18_16, basis_im_18_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_18_17, basis_im_18_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_18_18, basis_im_18_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_18_19, basis_im_18_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_18_20, basis_im_18_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_18_21, basis_im_18_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_18_22, basis_im_18_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_18_23, basis_im_18_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_18_24, basis_im_18_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
