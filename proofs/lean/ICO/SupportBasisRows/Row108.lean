import ICO.SupportBasisProducts.Row108
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_108 (b : Fin 25) :
    basisProductRe 108 b.val = (if 108 = 103+b.val then 1 else 0) ∧
    basisProductIm 108 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_108_0, basis_im_108_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_108_1, basis_im_108_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_108_2, basis_im_108_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_108_3, basis_im_108_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_108_4, basis_im_108_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_108_5, basis_im_108_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_108_6, basis_im_108_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_108_7, basis_im_108_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_108_8, basis_im_108_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_108_9, basis_im_108_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_108_10, basis_im_108_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_108_11, basis_im_108_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_108_12, basis_im_108_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_108_13, basis_im_108_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_108_14, basis_im_108_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_108_15, basis_im_108_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_108_16, basis_im_108_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_108_17, basis_im_108_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_108_18, basis_im_108_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_108_19, basis_im_108_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_108_20, basis_im_108_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_108_21, basis_im_108_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_108_22, basis_im_108_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_108_23, basis_im_108_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_108_24, basis_im_108_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
