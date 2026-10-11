import ICO.SupportBasisProducts.Row47
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_47 (b : Fin 25) :
    basisProductRe 47 b.val = (if 47 = 103+b.val then 1 else 0) ∧
    basisProductIm 47 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_47_0, basis_im_47_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_47_1, basis_im_47_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_47_2, basis_im_47_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_47_3, basis_im_47_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_47_4, basis_im_47_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_47_5, basis_im_47_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_47_6, basis_im_47_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_47_7, basis_im_47_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_47_8, basis_im_47_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_47_9, basis_im_47_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_47_10, basis_im_47_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_47_11, basis_im_47_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_47_12, basis_im_47_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_47_13, basis_im_47_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_47_14, basis_im_47_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_47_15, basis_im_47_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_47_16, basis_im_47_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_47_17, basis_im_47_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_47_18, basis_im_47_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_47_19, basis_im_47_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_47_20, basis_im_47_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_47_21, basis_im_47_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_47_22, basis_im_47_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_47_23, basis_im_47_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_47_24, basis_im_47_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
