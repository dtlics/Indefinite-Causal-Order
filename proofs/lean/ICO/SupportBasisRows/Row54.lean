import ICO.SupportBasisProducts.Row54
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_54 (b : Fin 25) :
    basisProductRe 54 b.val = (if 54 = 103+b.val then 1 else 0) ∧
    basisProductIm 54 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_54_0, basis_im_54_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_54_1, basis_im_54_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_54_2, basis_im_54_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_54_3, basis_im_54_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_54_4, basis_im_54_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_54_5, basis_im_54_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_54_6, basis_im_54_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_54_7, basis_im_54_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_54_8, basis_im_54_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_54_9, basis_im_54_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_54_10, basis_im_54_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_54_11, basis_im_54_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_54_12, basis_im_54_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_54_13, basis_im_54_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_54_14, basis_im_54_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_54_15, basis_im_54_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_54_16, basis_im_54_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_54_17, basis_im_54_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_54_18, basis_im_54_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_54_19, basis_im_54_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_54_20, basis_im_54_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_54_21, basis_im_54_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_54_22, basis_im_54_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_54_23, basis_im_54_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_54_24, basis_im_54_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
