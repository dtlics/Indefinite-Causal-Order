import ICO.SupportBasisProducts.Row41
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_41 (b : Fin 25) :
    basisProductRe 41 b.val = (if 41 = 103+b.val then 1 else 0) ∧
    basisProductIm 41 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_41_0, basis_im_41_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_41_1, basis_im_41_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_41_2, basis_im_41_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_41_3, basis_im_41_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_41_4, basis_im_41_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_41_5, basis_im_41_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_41_6, basis_im_41_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_41_7, basis_im_41_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_41_8, basis_im_41_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_41_9, basis_im_41_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_41_10, basis_im_41_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_41_11, basis_im_41_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_41_12, basis_im_41_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_41_13, basis_im_41_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_41_14, basis_im_41_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_41_15, basis_im_41_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_41_16, basis_im_41_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_41_17, basis_im_41_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_41_18, basis_im_41_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_41_19, basis_im_41_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_41_20, basis_im_41_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_41_21, basis_im_41_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_41_22, basis_im_41_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_41_23, basis_im_41_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_41_24, basis_im_41_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
