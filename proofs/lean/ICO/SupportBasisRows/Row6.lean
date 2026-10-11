import ICO.SupportBasisProducts.Row6
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_6 (b : Fin 25) :
    basisProductRe 6 b.val = (if 6 = 103+b.val then 1 else 0) ∧
    basisProductIm 6 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_6_0, basis_im_6_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_6_1, basis_im_6_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_6_2, basis_im_6_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_6_3, basis_im_6_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_6_4, basis_im_6_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_6_5, basis_im_6_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_6_6, basis_im_6_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_6_7, basis_im_6_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_6_8, basis_im_6_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_6_9, basis_im_6_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_6_10, basis_im_6_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_6_11, basis_im_6_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_6_12, basis_im_6_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_6_13, basis_im_6_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_6_14, basis_im_6_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_6_15, basis_im_6_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_6_16, basis_im_6_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_6_17, basis_im_6_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_6_18, basis_im_6_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_6_19, basis_im_6_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_6_20, basis_im_6_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_6_21, basis_im_6_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_6_22, basis_im_6_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_6_23, basis_im_6_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_6_24, basis_im_6_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
