import ICO.SupportBasisProducts.Row75
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_75 (b : Fin 25) :
    basisProductRe 75 b.val = (if 75 = 103+b.val then 1 else 0) ∧
    basisProductIm 75 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_75_0, basis_im_75_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_75_1, basis_im_75_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_75_2, basis_im_75_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_75_3, basis_im_75_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_75_4, basis_im_75_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_75_5, basis_im_75_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_75_6, basis_im_75_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_75_7, basis_im_75_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_75_8, basis_im_75_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_75_9, basis_im_75_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_75_10, basis_im_75_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_75_11, basis_im_75_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_75_12, basis_im_75_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_75_13, basis_im_75_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_75_14, basis_im_75_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_75_15, basis_im_75_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_75_16, basis_im_75_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_75_17, basis_im_75_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_75_18, basis_im_75_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_75_19, basis_im_75_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_75_20, basis_im_75_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_75_21, basis_im_75_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_75_22, basis_im_75_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_75_23, basis_im_75_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_75_24, basis_im_75_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
