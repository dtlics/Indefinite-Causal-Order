import ICO.SupportBasisProducts.Row17
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_17 (b : Fin 25) :
    basisProductRe 17 b.val = (if 17 = 103+b.val then 1 else 0) ∧
    basisProductIm 17 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_17_0, basis_im_17_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_17_1, basis_im_17_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_17_2, basis_im_17_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_17_3, basis_im_17_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_17_4, basis_im_17_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_17_5, basis_im_17_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_17_6, basis_im_17_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_17_7, basis_im_17_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_17_8, basis_im_17_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_17_9, basis_im_17_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_17_10, basis_im_17_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_17_11, basis_im_17_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_17_12, basis_im_17_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_17_13, basis_im_17_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_17_14, basis_im_17_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_17_15, basis_im_17_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_17_16, basis_im_17_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_17_17, basis_im_17_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_17_18, basis_im_17_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_17_19, basis_im_17_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_17_20, basis_im_17_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_17_21, basis_im_17_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_17_22, basis_im_17_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_17_23, basis_im_17_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_17_24, basis_im_17_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
