import ICO.SupportBasisProducts.Row11
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_11 (b : Fin 25) :
    basisProductRe 11 b.val = (if 11 = 103+b.val then 1 else 0) ∧
    basisProductIm 11 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_11_0, basis_im_11_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_11_1, basis_im_11_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_11_2, basis_im_11_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_11_3, basis_im_11_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_11_4, basis_im_11_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_11_5, basis_im_11_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_11_6, basis_im_11_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_11_7, basis_im_11_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_11_8, basis_im_11_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_11_9, basis_im_11_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_11_10, basis_im_11_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_11_11, basis_im_11_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_11_12, basis_im_11_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_11_13, basis_im_11_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_11_14, basis_im_11_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_11_15, basis_im_11_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_11_16, basis_im_11_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_11_17, basis_im_11_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_11_18, basis_im_11_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_11_19, basis_im_11_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_11_20, basis_im_11_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_11_21, basis_im_11_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_11_22, basis_im_11_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_11_23, basis_im_11_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_11_24, basis_im_11_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
