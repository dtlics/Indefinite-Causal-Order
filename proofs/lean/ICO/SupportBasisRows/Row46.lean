import ICO.SupportBasisProducts.Row46
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_46 (b : Fin 25) :
    basisProductRe 46 b.val = (if 46 = 103+b.val then 1 else 0) ∧
    basisProductIm 46 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_46_0, basis_im_46_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_46_1, basis_im_46_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_46_2, basis_im_46_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_46_3, basis_im_46_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_46_4, basis_im_46_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_46_5, basis_im_46_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_46_6, basis_im_46_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_46_7, basis_im_46_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_46_8, basis_im_46_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_46_9, basis_im_46_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_46_10, basis_im_46_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_46_11, basis_im_46_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_46_12, basis_im_46_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_46_13, basis_im_46_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_46_14, basis_im_46_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_46_15, basis_im_46_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_46_16, basis_im_46_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_46_17, basis_im_46_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_46_18, basis_im_46_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_46_19, basis_im_46_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_46_20, basis_im_46_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_46_21, basis_im_46_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_46_22, basis_im_46_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_46_23, basis_im_46_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_46_24, basis_im_46_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
