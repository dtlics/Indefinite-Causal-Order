import ICO.SupportBasisProducts.Row23
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_23 (b : Fin 25) :
    basisProductRe 23 b.val = (if 23 = 103+b.val then 1 else 0) ∧
    basisProductIm 23 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_23_0, basis_im_23_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_23_1, basis_im_23_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_23_2, basis_im_23_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_23_3, basis_im_23_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_23_4, basis_im_23_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_23_5, basis_im_23_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_23_6, basis_im_23_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_23_7, basis_im_23_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_23_8, basis_im_23_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_23_9, basis_im_23_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_23_10, basis_im_23_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_23_11, basis_im_23_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_23_12, basis_im_23_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_23_13, basis_im_23_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_23_14, basis_im_23_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_23_15, basis_im_23_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_23_16, basis_im_23_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_23_17, basis_im_23_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_23_18, basis_im_23_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_23_19, basis_im_23_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_23_20, basis_im_23_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_23_21, basis_im_23_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_23_22, basis_im_23_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_23_23, basis_im_23_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_23_24, basis_im_23_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
