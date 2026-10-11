import ICO.SupportBasisProducts.Row27
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_27 (b : Fin 25) :
    basisProductRe 27 b.val = (if 27 = 103+b.val then 1 else 0) ∧
    basisProductIm 27 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_27_0, basis_im_27_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_27_1, basis_im_27_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_27_2, basis_im_27_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_27_3, basis_im_27_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_27_4, basis_im_27_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_27_5, basis_im_27_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_27_6, basis_im_27_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_27_7, basis_im_27_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_27_8, basis_im_27_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_27_9, basis_im_27_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_27_10, basis_im_27_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_27_11, basis_im_27_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_27_12, basis_im_27_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_27_13, basis_im_27_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_27_14, basis_im_27_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_27_15, basis_im_27_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_27_16, basis_im_27_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_27_17, basis_im_27_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_27_18, basis_im_27_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_27_19, basis_im_27_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_27_20, basis_im_27_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_27_21, basis_im_27_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_27_22, basis_im_27_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_27_23, basis_im_27_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_27_24, basis_im_27_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
