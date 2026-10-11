import ICO.SupportBasisProducts.Row1
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_1 (b : Fin 25) :
    basisProductRe 1 b.val = (if 1 = 103+b.val then 1 else 0) ∧
    basisProductIm 1 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_1_0, basis_im_1_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_1_1, basis_im_1_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_1_2, basis_im_1_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_1_3, basis_im_1_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_1_4, basis_im_1_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_1_5, basis_im_1_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_1_6, basis_im_1_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_1_7, basis_im_1_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_1_8, basis_im_1_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_1_9, basis_im_1_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_1_10, basis_im_1_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_1_11, basis_im_1_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_1_12, basis_im_1_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_1_13, basis_im_1_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_1_14, basis_im_1_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_1_15, basis_im_1_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_1_16, basis_im_1_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_1_17, basis_im_1_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_1_18, basis_im_1_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_1_19, basis_im_1_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_1_20, basis_im_1_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_1_21, basis_im_1_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_1_22, basis_im_1_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_1_23, basis_im_1_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_1_24, basis_im_1_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
