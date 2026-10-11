import ICO.SupportBasisProducts.Row81
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_81 (b : Fin 25) :
    basisProductRe 81 b.val = (if 81 = 103+b.val then 1 else 0) ∧
    basisProductIm 81 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_81_0, basis_im_81_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_81_1, basis_im_81_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_81_2, basis_im_81_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_81_3, basis_im_81_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_81_4, basis_im_81_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_81_5, basis_im_81_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_81_6, basis_im_81_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_81_7, basis_im_81_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_81_8, basis_im_81_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_81_9, basis_im_81_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_81_10, basis_im_81_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_81_11, basis_im_81_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_81_12, basis_im_81_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_81_13, basis_im_81_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_81_14, basis_im_81_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_81_15, basis_im_81_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_81_16, basis_im_81_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_81_17, basis_im_81_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_81_18, basis_im_81_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_81_19, basis_im_81_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_81_20, basis_im_81_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_81_21, basis_im_81_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_81_22, basis_im_81_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_81_23, basis_im_81_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_81_24, basis_im_81_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
