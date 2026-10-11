import ICO.SupportBasisProducts.Row42
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_42 (b : Fin 25) :
    basisProductRe 42 b.val = (if 42 = 103+b.val then 1 else 0) ∧
    basisProductIm 42 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_42_0, basis_im_42_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_42_1, basis_im_42_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_42_2, basis_im_42_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_42_3, basis_im_42_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_42_4, basis_im_42_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_42_5, basis_im_42_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_42_6, basis_im_42_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_42_7, basis_im_42_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_42_8, basis_im_42_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_42_9, basis_im_42_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_42_10, basis_im_42_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_42_11, basis_im_42_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_42_12, basis_im_42_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_42_13, basis_im_42_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_42_14, basis_im_42_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_42_15, basis_im_42_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_42_16, basis_im_42_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_42_17, basis_im_42_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_42_18, basis_im_42_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_42_19, basis_im_42_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_42_20, basis_im_42_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_42_21, basis_im_42_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_42_22, basis_im_42_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_42_23, basis_im_42_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_42_24, basis_im_42_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
