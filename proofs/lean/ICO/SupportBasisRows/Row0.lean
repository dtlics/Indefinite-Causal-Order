import ICO.SupportBasisProducts.Row0
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_0 (b : Fin 25) :
    basisProductRe 0 b.val = (if 0 = 103+b.val then 1 else 0) ∧
    basisProductIm 0 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_0_0, basis_im_0_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_0_1, basis_im_0_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_0_2, basis_im_0_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_0_3, basis_im_0_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_0_4, basis_im_0_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_0_5, basis_im_0_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_0_6, basis_im_0_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_0_7, basis_im_0_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_0_8, basis_im_0_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_0_9, basis_im_0_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_0_10, basis_im_0_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_0_11, basis_im_0_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_0_12, basis_im_0_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_0_13, basis_im_0_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_0_14, basis_im_0_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_0_15, basis_im_0_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_0_16, basis_im_0_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_0_17, basis_im_0_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_0_18, basis_im_0_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_0_19, basis_im_0_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_0_20, basis_im_0_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_0_21, basis_im_0_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_0_22, basis_im_0_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_0_23, basis_im_0_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_0_24, basis_im_0_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
