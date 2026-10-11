import ICO.SupportBasisProducts.Row24
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_24 (b : Fin 25) :
    basisProductRe 24 b.val = (if 24 = 103+b.val then 1 else 0) ∧
    basisProductIm 24 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_24_0, basis_im_24_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_24_1, basis_im_24_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_24_2, basis_im_24_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_24_3, basis_im_24_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_24_4, basis_im_24_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_24_5, basis_im_24_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_24_6, basis_im_24_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_24_7, basis_im_24_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_24_8, basis_im_24_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_24_9, basis_im_24_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_24_10, basis_im_24_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_24_11, basis_im_24_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_24_12, basis_im_24_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_24_13, basis_im_24_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_24_14, basis_im_24_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_24_15, basis_im_24_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_24_16, basis_im_24_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_24_17, basis_im_24_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_24_18, basis_im_24_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_24_19, basis_im_24_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_24_20, basis_im_24_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_24_21, basis_im_24_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_24_22, basis_im_24_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_24_23, basis_im_24_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_24_24, basis_im_24_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
