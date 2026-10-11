import ICO.SupportBasisProducts.Row22
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_22 (b : Fin 25) :
    basisProductRe 22 b.val = (if 22 = 103+b.val then 1 else 0) ∧
    basisProductIm 22 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_22_0, basis_im_22_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_22_1, basis_im_22_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_22_2, basis_im_22_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_22_3, basis_im_22_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_22_4, basis_im_22_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_22_5, basis_im_22_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_22_6, basis_im_22_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_22_7, basis_im_22_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_22_8, basis_im_22_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_22_9, basis_im_22_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_22_10, basis_im_22_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_22_11, basis_im_22_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_22_12, basis_im_22_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_22_13, basis_im_22_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_22_14, basis_im_22_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_22_15, basis_im_22_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_22_16, basis_im_22_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_22_17, basis_im_22_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_22_18, basis_im_22_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_22_19, basis_im_22_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_22_20, basis_im_22_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_22_21, basis_im_22_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_22_22, basis_im_22_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_22_23, basis_im_22_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_22_24, basis_im_22_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
