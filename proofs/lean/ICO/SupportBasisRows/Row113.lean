import ICO.SupportBasisProducts.Row113
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_113 (b : Fin 25) :
    basisProductRe 113 b.val = (if 113 = 103+b.val then 1 else 0) ∧
    basisProductIm 113 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_113_0, basis_im_113_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_113_1, basis_im_113_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_113_2, basis_im_113_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_113_3, basis_im_113_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_113_4, basis_im_113_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_113_5, basis_im_113_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_113_6, basis_im_113_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_113_7, basis_im_113_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_113_8, basis_im_113_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_113_9, basis_im_113_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_113_10, basis_im_113_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_113_11, basis_im_113_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_113_12, basis_im_113_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_113_13, basis_im_113_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_113_14, basis_im_113_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_113_15, basis_im_113_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_113_16, basis_im_113_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_113_17, basis_im_113_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_113_18, basis_im_113_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_113_19, basis_im_113_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_113_20, basis_im_113_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_113_21, basis_im_113_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_113_22, basis_im_113_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_113_23, basis_im_113_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_113_24, basis_im_113_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
