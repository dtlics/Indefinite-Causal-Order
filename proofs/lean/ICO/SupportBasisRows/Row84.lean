import ICO.SupportBasisProducts.Row84
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_84 (b : Fin 25) :
    basisProductRe 84 b.val = (if 84 = 103+b.val then 1 else 0) ∧
    basisProductIm 84 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_84_0, basis_im_84_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_84_1, basis_im_84_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_84_2, basis_im_84_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_84_3, basis_im_84_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_84_4, basis_im_84_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_84_5, basis_im_84_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_84_6, basis_im_84_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_84_7, basis_im_84_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_84_8, basis_im_84_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_84_9, basis_im_84_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_84_10, basis_im_84_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_84_11, basis_im_84_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_84_12, basis_im_84_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_84_13, basis_im_84_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_84_14, basis_im_84_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_84_15, basis_im_84_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_84_16, basis_im_84_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_84_17, basis_im_84_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_84_18, basis_im_84_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_84_19, basis_im_84_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_84_20, basis_im_84_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_84_21, basis_im_84_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_84_22, basis_im_84_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_84_23, basis_im_84_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_84_24, basis_im_84_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
