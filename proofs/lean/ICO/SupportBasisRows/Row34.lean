import ICO.SupportBasisProducts.Row34
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_34 (b : Fin 25) :
    basisProductRe 34 b.val = (if 34 = 103+b.val then 1 else 0) ∧
    basisProductIm 34 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_34_0, basis_im_34_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_34_1, basis_im_34_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_34_2, basis_im_34_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_34_3, basis_im_34_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_34_4, basis_im_34_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_34_5, basis_im_34_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_34_6, basis_im_34_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_34_7, basis_im_34_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_34_8, basis_im_34_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_34_9, basis_im_34_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_34_10, basis_im_34_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_34_11, basis_im_34_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_34_12, basis_im_34_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_34_13, basis_im_34_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_34_14, basis_im_34_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_34_15, basis_im_34_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_34_16, basis_im_34_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_34_17, basis_im_34_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_34_18, basis_im_34_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_34_19, basis_im_34_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_34_20, basis_im_34_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_34_21, basis_im_34_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_34_22, basis_im_34_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_34_23, basis_im_34_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_34_24, basis_im_34_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
