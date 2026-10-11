import ICO.SupportBasisProducts.Row16
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_16 (b : Fin 25) :
    basisProductRe 16 b.val = (if 16 = 103+b.val then 1 else 0) ∧
    basisProductIm 16 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_16_0, basis_im_16_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_16_1, basis_im_16_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_16_2, basis_im_16_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_16_3, basis_im_16_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_16_4, basis_im_16_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_16_5, basis_im_16_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_16_6, basis_im_16_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_16_7, basis_im_16_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_16_8, basis_im_16_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_16_9, basis_im_16_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_16_10, basis_im_16_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_16_11, basis_im_16_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_16_12, basis_im_16_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_16_13, basis_im_16_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_16_14, basis_im_16_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_16_15, basis_im_16_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_16_16, basis_im_16_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_16_17, basis_im_16_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_16_18, basis_im_16_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_16_19, basis_im_16_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_16_20, basis_im_16_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_16_21, basis_im_16_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_16_22, basis_im_16_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_16_23, basis_im_16_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_16_24, basis_im_16_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
