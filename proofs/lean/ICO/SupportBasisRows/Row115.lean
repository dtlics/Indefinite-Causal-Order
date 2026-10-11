import ICO.SupportBasisProducts.Row115
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_115 (b : Fin 25) :
    basisProductRe 115 b.val = (if 115 = 103+b.val then 1 else 0) ∧
    basisProductIm 115 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_115_0, basis_im_115_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_115_1, basis_im_115_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_115_2, basis_im_115_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_115_3, basis_im_115_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_115_4, basis_im_115_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_115_5, basis_im_115_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_115_6, basis_im_115_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_115_7, basis_im_115_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_115_8, basis_im_115_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_115_9, basis_im_115_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_115_10, basis_im_115_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_115_11, basis_im_115_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_115_12, basis_im_115_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_115_13, basis_im_115_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_115_14, basis_im_115_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_115_15, basis_im_115_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_115_16, basis_im_115_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_115_17, basis_im_115_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_115_18, basis_im_115_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_115_19, basis_im_115_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_115_20, basis_im_115_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_115_21, basis_im_115_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_115_22, basis_im_115_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_115_23, basis_im_115_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_115_24, basis_im_115_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
