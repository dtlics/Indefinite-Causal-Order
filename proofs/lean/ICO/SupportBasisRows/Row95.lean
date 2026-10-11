import ICO.SupportBasisProducts.Row95
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_95 (b : Fin 25) :
    basisProductRe 95 b.val = (if 95 = 103+b.val then 1 else 0) ∧
    basisProductIm 95 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_95_0, basis_im_95_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_95_1, basis_im_95_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_95_2, basis_im_95_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_95_3, basis_im_95_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_95_4, basis_im_95_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_95_5, basis_im_95_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_95_6, basis_im_95_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_95_7, basis_im_95_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_95_8, basis_im_95_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_95_9, basis_im_95_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_95_10, basis_im_95_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_95_11, basis_im_95_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_95_12, basis_im_95_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_95_13, basis_im_95_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_95_14, basis_im_95_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_95_15, basis_im_95_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_95_16, basis_im_95_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_95_17, basis_im_95_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_95_18, basis_im_95_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_95_19, basis_im_95_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_95_20, basis_im_95_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_95_21, basis_im_95_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_95_22, basis_im_95_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_95_23, basis_im_95_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_95_24, basis_im_95_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
