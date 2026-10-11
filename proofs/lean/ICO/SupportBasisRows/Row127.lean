import ICO.SupportBasisProducts.Row127
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_127 (b : Fin 25) :
    basisProductRe 127 b.val = (if 127 = 103+b.val then 1 else 0) ∧
    basisProductIm 127 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_127_0, basis_im_127_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_127_1, basis_im_127_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_127_2, basis_im_127_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_127_3, basis_im_127_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_127_4, basis_im_127_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_127_5, basis_im_127_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_127_6, basis_im_127_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_127_7, basis_im_127_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_127_8, basis_im_127_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_127_9, basis_im_127_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_127_10, basis_im_127_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_127_11, basis_im_127_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_127_12, basis_im_127_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_127_13, basis_im_127_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_127_14, basis_im_127_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_127_15, basis_im_127_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_127_16, basis_im_127_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_127_17, basis_im_127_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_127_18, basis_im_127_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_127_19, basis_im_127_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_127_20, basis_im_127_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_127_21, basis_im_127_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_127_22, basis_im_127_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_127_23, basis_im_127_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_127_24, basis_im_127_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
