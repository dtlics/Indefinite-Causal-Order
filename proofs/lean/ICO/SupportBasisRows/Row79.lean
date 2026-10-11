import ICO.SupportBasisProducts.Row79
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_79 (b : Fin 25) :
    basisProductRe 79 b.val = (if 79 = 103+b.val then 1 else 0) ∧
    basisProductIm 79 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_79_0, basis_im_79_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_79_1, basis_im_79_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_79_2, basis_im_79_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_79_3, basis_im_79_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_79_4, basis_im_79_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_79_5, basis_im_79_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_79_6, basis_im_79_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_79_7, basis_im_79_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_79_8, basis_im_79_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_79_9, basis_im_79_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_79_10, basis_im_79_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_79_11, basis_im_79_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_79_12, basis_im_79_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_79_13, basis_im_79_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_79_14, basis_im_79_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_79_15, basis_im_79_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_79_16, basis_im_79_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_79_17, basis_im_79_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_79_18, basis_im_79_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_79_19, basis_im_79_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_79_20, basis_im_79_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_79_21, basis_im_79_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_79_22, basis_im_79_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_79_23, basis_im_79_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_79_24, basis_im_79_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
