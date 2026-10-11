import ICO.SupportBasisProducts.Row70
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_70 (b : Fin 25) :
    basisProductRe 70 b.val = (if 70 = 103+b.val then 1 else 0) ∧
    basisProductIm 70 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_70_0, basis_im_70_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_70_1, basis_im_70_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_70_2, basis_im_70_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_70_3, basis_im_70_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_70_4, basis_im_70_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_70_5, basis_im_70_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_70_6, basis_im_70_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_70_7, basis_im_70_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_70_8, basis_im_70_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_70_9, basis_im_70_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_70_10, basis_im_70_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_70_11, basis_im_70_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_70_12, basis_im_70_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_70_13, basis_im_70_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_70_14, basis_im_70_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_70_15, basis_im_70_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_70_16, basis_im_70_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_70_17, basis_im_70_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_70_18, basis_im_70_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_70_19, basis_im_70_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_70_20, basis_im_70_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_70_21, basis_im_70_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_70_22, basis_im_70_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_70_23, basis_im_70_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_70_24, basis_im_70_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
