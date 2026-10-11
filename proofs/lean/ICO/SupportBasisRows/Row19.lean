import ICO.SupportBasisProducts.Row19
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_19 (b : Fin 25) :
    basisProductRe 19 b.val = (if 19 = 103+b.val then 1 else 0) ∧
    basisProductIm 19 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_19_0, basis_im_19_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_19_1, basis_im_19_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_19_2, basis_im_19_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_19_3, basis_im_19_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_19_4, basis_im_19_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_19_5, basis_im_19_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_19_6, basis_im_19_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_19_7, basis_im_19_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_19_8, basis_im_19_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_19_9, basis_im_19_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_19_10, basis_im_19_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_19_11, basis_im_19_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_19_12, basis_im_19_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_19_13, basis_im_19_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_19_14, basis_im_19_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_19_15, basis_im_19_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_19_16, basis_im_19_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_19_17, basis_im_19_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_19_18, basis_im_19_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_19_19, basis_im_19_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_19_20, basis_im_19_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_19_21, basis_im_19_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_19_22, basis_im_19_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_19_23, basis_im_19_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_19_24, basis_im_19_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
