import ICO.SupportBasisProducts.Row123
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_123 (b : Fin 25) :
    basisProductRe 123 b.val = (if 123 = 103+b.val then 1 else 0) ∧
    basisProductIm 123 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_123_0, basis_im_123_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_123_1, basis_im_123_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_123_2, basis_im_123_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_123_3, basis_im_123_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_123_4, basis_im_123_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_123_5, basis_im_123_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_123_6, basis_im_123_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_123_7, basis_im_123_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_123_8, basis_im_123_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_123_9, basis_im_123_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_123_10, basis_im_123_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_123_11, basis_im_123_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_123_12, basis_im_123_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_123_13, basis_im_123_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_123_14, basis_im_123_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_123_15, basis_im_123_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_123_16, basis_im_123_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_123_17, basis_im_123_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_123_18, basis_im_123_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_123_19, basis_im_123_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_123_20, basis_im_123_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_123_21, basis_im_123_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_123_22, basis_im_123_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_123_23, basis_im_123_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_123_24, basis_im_123_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
