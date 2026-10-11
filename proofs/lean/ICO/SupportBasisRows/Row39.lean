import ICO.SupportBasisProducts.Row39
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_39 (b : Fin 25) :
    basisProductRe 39 b.val = (if 39 = 103+b.val then 1 else 0) ∧
    basisProductIm 39 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_39_0, basis_im_39_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_39_1, basis_im_39_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_39_2, basis_im_39_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_39_3, basis_im_39_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_39_4, basis_im_39_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_39_5, basis_im_39_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_39_6, basis_im_39_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_39_7, basis_im_39_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_39_8, basis_im_39_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_39_9, basis_im_39_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_39_10, basis_im_39_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_39_11, basis_im_39_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_39_12, basis_im_39_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_39_13, basis_im_39_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_39_14, basis_im_39_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_39_15, basis_im_39_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_39_16, basis_im_39_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_39_17, basis_im_39_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_39_18, basis_im_39_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_39_19, basis_im_39_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_39_20, basis_im_39_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_39_21, basis_im_39_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_39_22, basis_im_39_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_39_23, basis_im_39_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_39_24, basis_im_39_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
