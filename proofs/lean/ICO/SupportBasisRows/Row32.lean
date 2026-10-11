import ICO.SupportBasisProducts.Row32
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_32 (b : Fin 25) :
    basisProductRe 32 b.val = (if 32 = 103+b.val then 1 else 0) ∧
    basisProductIm 32 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_32_0, basis_im_32_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_32_1, basis_im_32_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_32_2, basis_im_32_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_32_3, basis_im_32_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_32_4, basis_im_32_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_32_5, basis_im_32_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_32_6, basis_im_32_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_32_7, basis_im_32_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_32_8, basis_im_32_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_32_9, basis_im_32_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_32_10, basis_im_32_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_32_11, basis_im_32_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_32_12, basis_im_32_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_32_13, basis_im_32_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_32_14, basis_im_32_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_32_15, basis_im_32_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_32_16, basis_im_32_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_32_17, basis_im_32_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_32_18, basis_im_32_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_32_19, basis_im_32_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_32_20, basis_im_32_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_32_21, basis_im_32_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_32_22, basis_im_32_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_32_23, basis_im_32_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_32_24, basis_im_32_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
