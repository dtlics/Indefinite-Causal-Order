import ICO.SupportBasisProducts.Row93
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_93 (b : Fin 25) :
    basisProductRe 93 b.val = (if 93 = 103+b.val then 1 else 0) ∧
    basisProductIm 93 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_93_0, basis_im_93_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_93_1, basis_im_93_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_93_2, basis_im_93_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_93_3, basis_im_93_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_93_4, basis_im_93_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_93_5, basis_im_93_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_93_6, basis_im_93_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_93_7, basis_im_93_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_93_8, basis_im_93_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_93_9, basis_im_93_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_93_10, basis_im_93_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_93_11, basis_im_93_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_93_12, basis_im_93_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_93_13, basis_im_93_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_93_14, basis_im_93_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_93_15, basis_im_93_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_93_16, basis_im_93_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_93_17, basis_im_93_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_93_18, basis_im_93_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_93_19, basis_im_93_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_93_20, basis_im_93_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_93_21, basis_im_93_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_93_22, basis_im_93_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_93_23, basis_im_93_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_93_24, basis_im_93_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
