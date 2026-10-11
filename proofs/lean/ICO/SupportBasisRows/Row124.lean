import ICO.SupportBasisProducts.Row124
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_124 (b : Fin 25) :
    basisProductRe 124 b.val = (if 124 = 103+b.val then 1 else 0) ∧
    basisProductIm 124 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_124_0, basis_im_124_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_124_1, basis_im_124_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_124_2, basis_im_124_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_124_3, basis_im_124_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_124_4, basis_im_124_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_124_5, basis_im_124_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_124_6, basis_im_124_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_124_7, basis_im_124_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_124_8, basis_im_124_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_124_9, basis_im_124_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_124_10, basis_im_124_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_124_11, basis_im_124_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_124_12, basis_im_124_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_124_13, basis_im_124_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_124_14, basis_im_124_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_124_15, basis_im_124_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_124_16, basis_im_124_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_124_17, basis_im_124_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_124_18, basis_im_124_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_124_19, basis_im_124_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_124_20, basis_im_124_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_124_21, basis_im_124_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_124_22, basis_im_124_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_124_23, basis_im_124_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_124_24, basis_im_124_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
