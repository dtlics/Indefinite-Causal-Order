import ICO.SupportBasisProducts.Row9
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_9 (b : Fin 25) :
    basisProductRe 9 b.val = (if 9 = 103+b.val then 1 else 0) ∧
    basisProductIm 9 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_9_0, basis_im_9_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_9_1, basis_im_9_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_9_2, basis_im_9_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_9_3, basis_im_9_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_9_4, basis_im_9_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_9_5, basis_im_9_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_9_6, basis_im_9_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_9_7, basis_im_9_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_9_8, basis_im_9_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_9_9, basis_im_9_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_9_10, basis_im_9_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_9_11, basis_im_9_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_9_12, basis_im_9_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_9_13, basis_im_9_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_9_14, basis_im_9_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_9_15, basis_im_9_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_9_16, basis_im_9_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_9_17, basis_im_9_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_9_18, basis_im_9_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_9_19, basis_im_9_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_9_20, basis_im_9_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_9_21, basis_im_9_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_9_22, basis_im_9_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_9_23, basis_im_9_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_9_24, basis_im_9_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
