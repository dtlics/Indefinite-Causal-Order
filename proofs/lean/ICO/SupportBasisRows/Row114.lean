import ICO.SupportBasisProducts.Row114
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_114 (b : Fin 25) :
    basisProductRe 114 b.val = (if 114 = 103+b.val then 1 else 0) ∧
    basisProductIm 114 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_114_0, basis_im_114_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_114_1, basis_im_114_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_114_2, basis_im_114_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_114_3, basis_im_114_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_114_4, basis_im_114_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_114_5, basis_im_114_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_114_6, basis_im_114_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_114_7, basis_im_114_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_114_8, basis_im_114_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_114_9, basis_im_114_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_114_10, basis_im_114_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_114_11, basis_im_114_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_114_12, basis_im_114_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_114_13, basis_im_114_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_114_14, basis_im_114_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_114_15, basis_im_114_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_114_16, basis_im_114_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_114_17, basis_im_114_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_114_18, basis_im_114_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_114_19, basis_im_114_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_114_20, basis_im_114_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_114_21, basis_im_114_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_114_22, basis_im_114_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_114_23, basis_im_114_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_114_24, basis_im_114_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
