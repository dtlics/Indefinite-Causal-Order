import ICO.SupportBasisProducts.Row58
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_58 (b : Fin 25) :
    basisProductRe 58 b.val = (if 58 = 103+b.val then 1 else 0) ∧
    basisProductIm 58 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_58_0, basis_im_58_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_58_1, basis_im_58_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_58_2, basis_im_58_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_58_3, basis_im_58_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_58_4, basis_im_58_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_58_5, basis_im_58_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_58_6, basis_im_58_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_58_7, basis_im_58_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_58_8, basis_im_58_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_58_9, basis_im_58_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_58_10, basis_im_58_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_58_11, basis_im_58_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_58_12, basis_im_58_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_58_13, basis_im_58_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_58_14, basis_im_58_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_58_15, basis_im_58_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_58_16, basis_im_58_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_58_17, basis_im_58_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_58_18, basis_im_58_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_58_19, basis_im_58_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_58_20, basis_im_58_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_58_21, basis_im_58_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_58_22, basis_im_58_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_58_23, basis_im_58_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_58_24, basis_im_58_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
