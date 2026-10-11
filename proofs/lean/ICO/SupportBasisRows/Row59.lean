import ICO.SupportBasisProducts.Row59
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_59 (b : Fin 25) :
    basisProductRe 59 b.val = (if 59 = 103+b.val then 1 else 0) ∧
    basisProductIm 59 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_59_0, basis_im_59_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_59_1, basis_im_59_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_59_2, basis_im_59_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_59_3, basis_im_59_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_59_4, basis_im_59_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_59_5, basis_im_59_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_59_6, basis_im_59_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_59_7, basis_im_59_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_59_8, basis_im_59_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_59_9, basis_im_59_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_59_10, basis_im_59_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_59_11, basis_im_59_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_59_12, basis_im_59_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_59_13, basis_im_59_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_59_14, basis_im_59_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_59_15, basis_im_59_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_59_16, basis_im_59_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_59_17, basis_im_59_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_59_18, basis_im_59_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_59_19, basis_im_59_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_59_20, basis_im_59_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_59_21, basis_im_59_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_59_22, basis_im_59_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_59_23, basis_im_59_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_59_24, basis_im_59_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
