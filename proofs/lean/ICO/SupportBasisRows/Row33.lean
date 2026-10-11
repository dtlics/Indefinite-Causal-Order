import ICO.SupportBasisProducts.Row33
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_33 (b : Fin 25) :
    basisProductRe 33 b.val = (if 33 = 103+b.val then 1 else 0) ∧
    basisProductIm 33 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_33_0, basis_im_33_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_33_1, basis_im_33_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_33_2, basis_im_33_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_33_3, basis_im_33_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_33_4, basis_im_33_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_33_5, basis_im_33_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_33_6, basis_im_33_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_33_7, basis_im_33_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_33_8, basis_im_33_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_33_9, basis_im_33_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_33_10, basis_im_33_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_33_11, basis_im_33_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_33_12, basis_im_33_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_33_13, basis_im_33_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_33_14, basis_im_33_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_33_15, basis_im_33_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_33_16, basis_im_33_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_33_17, basis_im_33_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_33_18, basis_im_33_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_33_19, basis_im_33_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_33_20, basis_im_33_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_33_21, basis_im_33_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_33_22, basis_im_33_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_33_23, basis_im_33_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_33_24, basis_im_33_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
