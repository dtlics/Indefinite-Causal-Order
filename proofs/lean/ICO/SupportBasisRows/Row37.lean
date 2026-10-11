import ICO.SupportBasisProducts.Row37
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_37 (b : Fin 25) :
    basisProductRe 37 b.val = (if 37 = 103+b.val then 1 else 0) ∧
    basisProductIm 37 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_37_0, basis_im_37_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_37_1, basis_im_37_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_37_2, basis_im_37_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_37_3, basis_im_37_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_37_4, basis_im_37_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_37_5, basis_im_37_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_37_6, basis_im_37_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_37_7, basis_im_37_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_37_8, basis_im_37_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_37_9, basis_im_37_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_37_10, basis_im_37_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_37_11, basis_im_37_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_37_12, basis_im_37_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_37_13, basis_im_37_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_37_14, basis_im_37_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_37_15, basis_im_37_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_37_16, basis_im_37_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_37_17, basis_im_37_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_37_18, basis_im_37_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_37_19, basis_im_37_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_37_20, basis_im_37_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_37_21, basis_im_37_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_37_22, basis_im_37_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_37_23, basis_im_37_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_37_24, basis_im_37_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
