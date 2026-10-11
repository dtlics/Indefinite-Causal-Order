import ICO.SupportBasisProducts.Row53
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_53 (b : Fin 25) :
    basisProductRe 53 b.val = (if 53 = 103+b.val then 1 else 0) ∧
    basisProductIm 53 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_53_0, basis_im_53_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_53_1, basis_im_53_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_53_2, basis_im_53_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_53_3, basis_im_53_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_53_4, basis_im_53_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_53_5, basis_im_53_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_53_6, basis_im_53_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_53_7, basis_im_53_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_53_8, basis_im_53_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_53_9, basis_im_53_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_53_10, basis_im_53_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_53_11, basis_im_53_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_53_12, basis_im_53_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_53_13, basis_im_53_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_53_14, basis_im_53_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_53_15, basis_im_53_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_53_16, basis_im_53_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_53_17, basis_im_53_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_53_18, basis_im_53_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_53_19, basis_im_53_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_53_20, basis_im_53_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_53_21, basis_im_53_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_53_22, basis_im_53_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_53_23, basis_im_53_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_53_24, basis_im_53_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
