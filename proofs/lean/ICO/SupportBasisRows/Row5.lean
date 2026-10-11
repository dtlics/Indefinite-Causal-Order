import ICO.SupportBasisProducts.Row5
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_5 (b : Fin 25) :
    basisProductRe 5 b.val = (if 5 = 103+b.val then 1 else 0) ∧
    basisProductIm 5 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_5_0, basis_im_5_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_5_1, basis_im_5_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_5_2, basis_im_5_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_5_3, basis_im_5_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_5_4, basis_im_5_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_5_5, basis_im_5_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_5_6, basis_im_5_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_5_7, basis_im_5_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_5_8, basis_im_5_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_5_9, basis_im_5_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_5_10, basis_im_5_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_5_11, basis_im_5_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_5_12, basis_im_5_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_5_13, basis_im_5_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_5_14, basis_im_5_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_5_15, basis_im_5_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_5_16, basis_im_5_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_5_17, basis_im_5_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_5_18, basis_im_5_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_5_19, basis_im_5_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_5_20, basis_im_5_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_5_21, basis_im_5_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_5_22, basis_im_5_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_5_23, basis_im_5_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_5_24, basis_im_5_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
