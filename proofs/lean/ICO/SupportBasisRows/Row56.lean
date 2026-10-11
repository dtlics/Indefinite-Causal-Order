import ICO.SupportBasisProducts.Row56
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_56 (b : Fin 25) :
    basisProductRe 56 b.val = (if 56 = 103+b.val then 1 else 0) ∧
    basisProductIm 56 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_56_0, basis_im_56_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_56_1, basis_im_56_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_56_2, basis_im_56_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_56_3, basis_im_56_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_56_4, basis_im_56_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_56_5, basis_im_56_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_56_6, basis_im_56_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_56_7, basis_im_56_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_56_8, basis_im_56_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_56_9, basis_im_56_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_56_10, basis_im_56_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_56_11, basis_im_56_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_56_12, basis_im_56_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_56_13, basis_im_56_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_56_14, basis_im_56_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_56_15, basis_im_56_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_56_16, basis_im_56_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_56_17, basis_im_56_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_56_18, basis_im_56_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_56_19, basis_im_56_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_56_20, basis_im_56_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_56_21, basis_im_56_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_56_22, basis_im_56_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_56_23, basis_im_56_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_56_24, basis_im_56_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
