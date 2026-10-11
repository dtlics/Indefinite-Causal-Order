import ICO.SupportBasisProducts.Row30
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_30 (b : Fin 25) :
    basisProductRe 30 b.val = (if 30 = 103+b.val then 1 else 0) ∧
    basisProductIm 30 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_30_0, basis_im_30_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_30_1, basis_im_30_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_30_2, basis_im_30_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_30_3, basis_im_30_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_30_4, basis_im_30_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_30_5, basis_im_30_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_30_6, basis_im_30_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_30_7, basis_im_30_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_30_8, basis_im_30_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_30_9, basis_im_30_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_30_10, basis_im_30_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_30_11, basis_im_30_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_30_12, basis_im_30_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_30_13, basis_im_30_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_30_14, basis_im_30_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_30_15, basis_im_30_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_30_16, basis_im_30_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_30_17, basis_im_30_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_30_18, basis_im_30_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_30_19, basis_im_30_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_30_20, basis_im_30_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_30_21, basis_im_30_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_30_22, basis_im_30_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_30_23, basis_im_30_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_30_24, basis_im_30_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
