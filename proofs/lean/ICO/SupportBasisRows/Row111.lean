import ICO.SupportBasisProducts.Row111
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_111 (b : Fin 25) :
    basisProductRe 111 b.val = (if 111 = 103+b.val then 1 else 0) ∧
    basisProductIm 111 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_111_0, basis_im_111_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_111_1, basis_im_111_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_111_2, basis_im_111_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_111_3, basis_im_111_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_111_4, basis_im_111_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_111_5, basis_im_111_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_111_6, basis_im_111_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_111_7, basis_im_111_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_111_8, basis_im_111_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_111_9, basis_im_111_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_111_10, basis_im_111_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_111_11, basis_im_111_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_111_12, basis_im_111_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_111_13, basis_im_111_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_111_14, basis_im_111_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_111_15, basis_im_111_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_111_16, basis_im_111_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_111_17, basis_im_111_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_111_18, basis_im_111_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_111_19, basis_im_111_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_111_20, basis_im_111_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_111_21, basis_im_111_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_111_22, basis_im_111_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_111_23, basis_im_111_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_111_24, basis_im_111_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
