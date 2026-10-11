import ICO.SupportBasisProducts.Row99
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_99 (b : Fin 25) :
    basisProductRe 99 b.val = (if 99 = 103+b.val then 1 else 0) ∧
    basisProductIm 99 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_99_0, basis_im_99_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_99_1, basis_im_99_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_99_2, basis_im_99_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_99_3, basis_im_99_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_99_4, basis_im_99_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_99_5, basis_im_99_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_99_6, basis_im_99_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_99_7, basis_im_99_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_99_8, basis_im_99_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_99_9, basis_im_99_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_99_10, basis_im_99_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_99_11, basis_im_99_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_99_12, basis_im_99_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_99_13, basis_im_99_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_99_14, basis_im_99_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_99_15, basis_im_99_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_99_16, basis_im_99_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_99_17, basis_im_99_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_99_18, basis_im_99_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_99_19, basis_im_99_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_99_20, basis_im_99_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_99_21, basis_im_99_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_99_22, basis_im_99_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_99_23, basis_im_99_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_99_24, basis_im_99_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
