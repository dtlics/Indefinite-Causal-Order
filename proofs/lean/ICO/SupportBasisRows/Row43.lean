import ICO.SupportBasisProducts.Row43
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_43 (b : Fin 25) :
    basisProductRe 43 b.val = (if 43 = 103+b.val then 1 else 0) ∧
    basisProductIm 43 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_43_0, basis_im_43_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_43_1, basis_im_43_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_43_2, basis_im_43_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_43_3, basis_im_43_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_43_4, basis_im_43_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_43_5, basis_im_43_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_43_6, basis_im_43_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_43_7, basis_im_43_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_43_8, basis_im_43_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_43_9, basis_im_43_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_43_10, basis_im_43_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_43_11, basis_im_43_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_43_12, basis_im_43_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_43_13, basis_im_43_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_43_14, basis_im_43_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_43_15, basis_im_43_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_43_16, basis_im_43_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_43_17, basis_im_43_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_43_18, basis_im_43_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_43_19, basis_im_43_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_43_20, basis_im_43_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_43_21, basis_im_43_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_43_22, basis_im_43_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_43_23, basis_im_43_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_43_24, basis_im_43_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
