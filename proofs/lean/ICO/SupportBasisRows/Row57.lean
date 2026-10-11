import ICO.SupportBasisProducts.Row57
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_57 (b : Fin 25) :
    basisProductRe 57 b.val = (if 57 = 103+b.val then 1 else 0) ∧
    basisProductIm 57 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_57_0, basis_im_57_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_57_1, basis_im_57_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_57_2, basis_im_57_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_57_3, basis_im_57_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_57_4, basis_im_57_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_57_5, basis_im_57_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_57_6, basis_im_57_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_57_7, basis_im_57_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_57_8, basis_im_57_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_57_9, basis_im_57_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_57_10, basis_im_57_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_57_11, basis_im_57_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_57_12, basis_im_57_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_57_13, basis_im_57_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_57_14, basis_im_57_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_57_15, basis_im_57_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_57_16, basis_im_57_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_57_17, basis_im_57_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_57_18, basis_im_57_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_57_19, basis_im_57_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_57_20, basis_im_57_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_57_21, basis_im_57_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_57_22, basis_im_57_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_57_23, basis_im_57_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_57_24, basis_im_57_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
