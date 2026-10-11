import ICO.SupportBasisProducts.Row8
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_8 (b : Fin 25) :
    basisProductRe 8 b.val = (if 8 = 103+b.val then 1 else 0) ∧
    basisProductIm 8 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_8_0, basis_im_8_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_8_1, basis_im_8_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_8_2, basis_im_8_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_8_3, basis_im_8_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_8_4, basis_im_8_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_8_5, basis_im_8_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_8_6, basis_im_8_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_8_7, basis_im_8_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_8_8, basis_im_8_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_8_9, basis_im_8_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_8_10, basis_im_8_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_8_11, basis_im_8_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_8_12, basis_im_8_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_8_13, basis_im_8_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_8_14, basis_im_8_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_8_15, basis_im_8_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_8_16, basis_im_8_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_8_17, basis_im_8_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_8_18, basis_im_8_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_8_19, basis_im_8_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_8_20, basis_im_8_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_8_21, basis_im_8_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_8_22, basis_im_8_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_8_23, basis_im_8_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_8_24, basis_im_8_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
