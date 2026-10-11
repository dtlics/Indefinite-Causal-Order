import ICO.SupportBasisProducts.Row3
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_3 (b : Fin 25) :
    basisProductRe 3 b.val = (if 3 = 103+b.val then 1 else 0) ∧
    basisProductIm 3 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_3_0, basis_im_3_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_3_1, basis_im_3_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_3_2, basis_im_3_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_3_3, basis_im_3_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_3_4, basis_im_3_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_3_5, basis_im_3_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_3_6, basis_im_3_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_3_7, basis_im_3_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_3_8, basis_im_3_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_3_9, basis_im_3_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_3_10, basis_im_3_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_3_11, basis_im_3_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_3_12, basis_im_3_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_3_13, basis_im_3_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_3_14, basis_im_3_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_3_15, basis_im_3_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_3_16, basis_im_3_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_3_17, basis_im_3_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_3_18, basis_im_3_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_3_19, basis_im_3_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_3_20, basis_im_3_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_3_21, basis_im_3_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_3_22, basis_im_3_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_3_23, basis_im_3_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_3_24, basis_im_3_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
