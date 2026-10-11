import ICO.SupportBasisProducts.Row10
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_10 (b : Fin 25) :
    basisProductRe 10 b.val = (if 10 = 103+b.val then 1 else 0) ∧
    basisProductIm 10 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_10_0, basis_im_10_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_10_1, basis_im_10_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_10_2, basis_im_10_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_10_3, basis_im_10_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_10_4, basis_im_10_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_10_5, basis_im_10_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_10_6, basis_im_10_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_10_7, basis_im_10_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_10_8, basis_im_10_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_10_9, basis_im_10_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_10_10, basis_im_10_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_10_11, basis_im_10_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_10_12, basis_im_10_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_10_13, basis_im_10_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_10_14, basis_im_10_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_10_15, basis_im_10_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_10_16, basis_im_10_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_10_17, basis_im_10_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_10_18, basis_im_10_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_10_19, basis_im_10_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_10_20, basis_im_10_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_10_21, basis_im_10_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_10_22, basis_im_10_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_10_23, basis_im_10_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_10_24, basis_im_10_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
