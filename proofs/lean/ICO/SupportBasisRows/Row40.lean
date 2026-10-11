import ICO.SupportBasisProducts.Row40
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_40 (b : Fin 25) :
    basisProductRe 40 b.val = (if 40 = 103+b.val then 1 else 0) ∧
    basisProductIm 40 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_40_0, basis_im_40_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_40_1, basis_im_40_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_40_2, basis_im_40_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_40_3, basis_im_40_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_40_4, basis_im_40_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_40_5, basis_im_40_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_40_6, basis_im_40_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_40_7, basis_im_40_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_40_8, basis_im_40_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_40_9, basis_im_40_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_40_10, basis_im_40_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_40_11, basis_im_40_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_40_12, basis_im_40_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_40_13, basis_im_40_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_40_14, basis_im_40_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_40_15, basis_im_40_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_40_16, basis_im_40_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_40_17, basis_im_40_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_40_18, basis_im_40_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_40_19, basis_im_40_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_40_20, basis_im_40_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_40_21, basis_im_40_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_40_22, basis_im_40_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_40_23, basis_im_40_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_40_24, basis_im_40_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
