import ICO.SupportBasisProducts.Row66
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_66 (b : Fin 25) :
    basisProductRe 66 b.val = (if 66 = 103+b.val then 1 else 0) ∧
    basisProductIm 66 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_66_0, basis_im_66_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_66_1, basis_im_66_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_66_2, basis_im_66_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_66_3, basis_im_66_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_66_4, basis_im_66_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_66_5, basis_im_66_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_66_6, basis_im_66_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_66_7, basis_im_66_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_66_8, basis_im_66_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_66_9, basis_im_66_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_66_10, basis_im_66_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_66_11, basis_im_66_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_66_12, basis_im_66_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_66_13, basis_im_66_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_66_14, basis_im_66_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_66_15, basis_im_66_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_66_16, basis_im_66_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_66_17, basis_im_66_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_66_18, basis_im_66_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_66_19, basis_im_66_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_66_20, basis_im_66_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_66_21, basis_im_66_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_66_22, basis_im_66_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_66_23, basis_im_66_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_66_24, basis_im_66_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
