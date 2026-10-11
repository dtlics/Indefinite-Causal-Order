import ICO.SupportBasisProducts.Row2
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_2 (b : Fin 25) :
    basisProductRe 2 b.val = (if 2 = 103+b.val then 1 else 0) ∧
    basisProductIm 2 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_2_0, basis_im_2_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_2_1, basis_im_2_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_2_2, basis_im_2_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_2_3, basis_im_2_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_2_4, basis_im_2_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_2_5, basis_im_2_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_2_6, basis_im_2_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_2_7, basis_im_2_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_2_8, basis_im_2_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_2_9, basis_im_2_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_2_10, basis_im_2_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_2_11, basis_im_2_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_2_12, basis_im_2_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_2_13, basis_im_2_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_2_14, basis_im_2_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_2_15, basis_im_2_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_2_16, basis_im_2_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_2_17, basis_im_2_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_2_18, basis_im_2_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_2_19, basis_im_2_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_2_20, basis_im_2_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_2_21, basis_im_2_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_2_22, basis_im_2_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_2_23, basis_im_2_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_2_24, basis_im_2_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
