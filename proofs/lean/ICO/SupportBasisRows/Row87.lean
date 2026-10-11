import ICO.SupportBasisProducts.Row87
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_87 (b : Fin 25) :
    basisProductRe 87 b.val = (if 87 = 103+b.val then 1 else 0) ∧
    basisProductIm 87 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_87_0, basis_im_87_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_87_1, basis_im_87_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_87_2, basis_im_87_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_87_3, basis_im_87_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_87_4, basis_im_87_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_87_5, basis_im_87_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_87_6, basis_im_87_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_87_7, basis_im_87_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_87_8, basis_im_87_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_87_9, basis_im_87_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_87_10, basis_im_87_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_87_11, basis_im_87_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_87_12, basis_im_87_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_87_13, basis_im_87_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_87_14, basis_im_87_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_87_15, basis_im_87_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_87_16, basis_im_87_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_87_17, basis_im_87_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_87_18, basis_im_87_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_87_19, basis_im_87_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_87_20, basis_im_87_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_87_21, basis_im_87_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_87_22, basis_im_87_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_87_23, basis_im_87_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_87_24, basis_im_87_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
