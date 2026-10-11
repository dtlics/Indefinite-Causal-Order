import ICO.SupportBasisProducts.Row103
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_103 (b : Fin 25) :
    basisProductRe 103 b.val = (if 103 = 103+b.val then 1 else 0) ∧
    basisProductIm 103 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_103_0, basis_im_103_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_103_1, basis_im_103_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_103_2, basis_im_103_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_103_3, basis_im_103_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_103_4, basis_im_103_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_103_5, basis_im_103_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_103_6, basis_im_103_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_103_7, basis_im_103_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_103_8, basis_im_103_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_103_9, basis_im_103_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_103_10, basis_im_103_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_103_11, basis_im_103_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_103_12, basis_im_103_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_103_13, basis_im_103_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_103_14, basis_im_103_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_103_15, basis_im_103_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_103_16, basis_im_103_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_103_17, basis_im_103_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_103_18, basis_im_103_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_103_19, basis_im_103_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_103_20, basis_im_103_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_103_21, basis_im_103_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_103_22, basis_im_103_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_103_23, basis_im_103_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_103_24, basis_im_103_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
