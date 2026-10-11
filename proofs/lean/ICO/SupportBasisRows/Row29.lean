import ICO.SupportBasisProducts.Row29
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_29 (b : Fin 25) :
    basisProductRe 29 b.val = (if 29 = 103+b.val then 1 else 0) ∧
    basisProductIm 29 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_29_0, basis_im_29_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_29_1, basis_im_29_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_29_2, basis_im_29_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_29_3, basis_im_29_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_29_4, basis_im_29_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_29_5, basis_im_29_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_29_6, basis_im_29_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_29_7, basis_im_29_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_29_8, basis_im_29_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_29_9, basis_im_29_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_29_10, basis_im_29_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_29_11, basis_im_29_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_29_12, basis_im_29_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_29_13, basis_im_29_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_29_14, basis_im_29_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_29_15, basis_im_29_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_29_16, basis_im_29_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_29_17, basis_im_29_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_29_18, basis_im_29_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_29_19, basis_im_29_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_29_20, basis_im_29_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_29_21, basis_im_29_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_29_22, basis_im_29_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_29_23, basis_im_29_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_29_24, basis_im_29_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
