import ICO.SupportBasisProducts.Row49
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_49 (b : Fin 25) :
    basisProductRe 49 b.val = (if 49 = 103+b.val then 1 else 0) ∧
    basisProductIm 49 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_49_0, basis_im_49_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_49_1, basis_im_49_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_49_2, basis_im_49_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_49_3, basis_im_49_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_49_4, basis_im_49_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_49_5, basis_im_49_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_49_6, basis_im_49_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_49_7, basis_im_49_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_49_8, basis_im_49_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_49_9, basis_im_49_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_49_10, basis_im_49_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_49_11, basis_im_49_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_49_12, basis_im_49_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_49_13, basis_im_49_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_49_14, basis_im_49_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_49_15, basis_im_49_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_49_16, basis_im_49_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_49_17, basis_im_49_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_49_18, basis_im_49_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_49_19, basis_im_49_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_49_20, basis_im_49_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_49_21, basis_im_49_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_49_22, basis_im_49_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_49_23, basis_im_49_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_49_24, basis_im_49_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
