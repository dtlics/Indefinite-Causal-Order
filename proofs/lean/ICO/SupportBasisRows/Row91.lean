import ICO.SupportBasisProducts.Row91
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_91 (b : Fin 25) :
    basisProductRe 91 b.val = (if 91 = 103+b.val then 1 else 0) ∧
    basisProductIm 91 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_91_0, basis_im_91_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_91_1, basis_im_91_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_91_2, basis_im_91_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_91_3, basis_im_91_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_91_4, basis_im_91_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_91_5, basis_im_91_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_91_6, basis_im_91_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_91_7, basis_im_91_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_91_8, basis_im_91_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_91_9, basis_im_91_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_91_10, basis_im_91_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_91_11, basis_im_91_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_91_12, basis_im_91_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_91_13, basis_im_91_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_91_14, basis_im_91_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_91_15, basis_im_91_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_91_16, basis_im_91_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_91_17, basis_im_91_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_91_18, basis_im_91_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_91_19, basis_im_91_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_91_20, basis_im_91_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_91_21, basis_im_91_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_91_22, basis_im_91_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_91_23, basis_im_91_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_91_24, basis_im_91_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
