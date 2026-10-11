import ICO.SupportBasisProducts.Row15
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_15 (b : Fin 25) :
    basisProductRe 15 b.val = (if 15 = 103+b.val then 1 else 0) ∧
    basisProductIm 15 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_15_0, basis_im_15_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_15_1, basis_im_15_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_15_2, basis_im_15_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_15_3, basis_im_15_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_15_4, basis_im_15_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_15_5, basis_im_15_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_15_6, basis_im_15_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_15_7, basis_im_15_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_15_8, basis_im_15_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_15_9, basis_im_15_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_15_10, basis_im_15_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_15_11, basis_im_15_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_15_12, basis_im_15_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_15_13, basis_im_15_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_15_14, basis_im_15_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_15_15, basis_im_15_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_15_16, basis_im_15_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_15_17, basis_im_15_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_15_18, basis_im_15_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_15_19, basis_im_15_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_15_20, basis_im_15_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_15_21, basis_im_15_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_15_22, basis_im_15_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_15_23, basis_im_15_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_15_24, basis_im_15_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
