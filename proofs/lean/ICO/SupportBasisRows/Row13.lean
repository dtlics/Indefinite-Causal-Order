import ICO.SupportBasisProducts.Row13
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_13 (b : Fin 25) :
    basisProductRe 13 b.val = (if 13 = 103+b.val then 1 else 0) ∧
    basisProductIm 13 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_13_0, basis_im_13_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_13_1, basis_im_13_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_13_2, basis_im_13_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_13_3, basis_im_13_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_13_4, basis_im_13_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_13_5, basis_im_13_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_13_6, basis_im_13_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_13_7, basis_im_13_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_13_8, basis_im_13_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_13_9, basis_im_13_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_13_10, basis_im_13_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_13_11, basis_im_13_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_13_12, basis_im_13_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_13_13, basis_im_13_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_13_14, basis_im_13_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_13_15, basis_im_13_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_13_16, basis_im_13_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_13_17, basis_im_13_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_13_18, basis_im_13_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_13_19, basis_im_13_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_13_20, basis_im_13_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_13_21, basis_im_13_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_13_22, basis_im_13_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_13_23, basis_im_13_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_13_24, basis_im_13_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
