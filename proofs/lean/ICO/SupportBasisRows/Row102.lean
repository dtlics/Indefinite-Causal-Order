import ICO.SupportBasisProducts.Row102
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_102 (b : Fin 25) :
    basisProductRe 102 b.val = (if 102 = 103+b.val then 1 else 0) ∧
    basisProductIm 102 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_102_0, basis_im_102_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_102_1, basis_im_102_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_102_2, basis_im_102_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_102_3, basis_im_102_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_102_4, basis_im_102_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_102_5, basis_im_102_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_102_6, basis_im_102_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_102_7, basis_im_102_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_102_8, basis_im_102_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_102_9, basis_im_102_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_102_10, basis_im_102_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_102_11, basis_im_102_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_102_12, basis_im_102_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_102_13, basis_im_102_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_102_14, basis_im_102_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_102_15, basis_im_102_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_102_16, basis_im_102_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_102_17, basis_im_102_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_102_18, basis_im_102_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_102_19, basis_im_102_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_102_20, basis_im_102_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_102_21, basis_im_102_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_102_22, basis_im_102_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_102_23, basis_im_102_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_102_24, basis_im_102_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
