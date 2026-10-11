import ICO.SupportBasisProducts.Row120
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_120 (b : Fin 25) :
    basisProductRe 120 b.val = (if 120 = 103+b.val then 1 else 0) ∧
    basisProductIm 120 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_120_0, basis_im_120_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_120_1, basis_im_120_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_120_2, basis_im_120_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_120_3, basis_im_120_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_120_4, basis_im_120_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_120_5, basis_im_120_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_120_6, basis_im_120_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_120_7, basis_im_120_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_120_8, basis_im_120_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_120_9, basis_im_120_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_120_10, basis_im_120_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_120_11, basis_im_120_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_120_12, basis_im_120_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_120_13, basis_im_120_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_120_14, basis_im_120_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_120_15, basis_im_120_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_120_16, basis_im_120_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_120_17, basis_im_120_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_120_18, basis_im_120_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_120_19, basis_im_120_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_120_20, basis_im_120_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_120_21, basis_im_120_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_120_22, basis_im_120_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_120_23, basis_im_120_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_120_24, basis_im_120_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
