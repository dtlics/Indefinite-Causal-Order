import ICO.SupportBasisProducts.Row116
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_116 (b : Fin 25) :
    basisProductRe 116 b.val = (if 116 = 103+b.val then 1 else 0) ∧
    basisProductIm 116 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_116_0, basis_im_116_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_116_1, basis_im_116_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_116_2, basis_im_116_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_116_3, basis_im_116_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_116_4, basis_im_116_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_116_5, basis_im_116_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_116_6, basis_im_116_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_116_7, basis_im_116_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_116_8, basis_im_116_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_116_9, basis_im_116_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_116_10, basis_im_116_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_116_11, basis_im_116_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_116_12, basis_im_116_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_116_13, basis_im_116_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_116_14, basis_im_116_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_116_15, basis_im_116_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_116_16, basis_im_116_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_116_17, basis_im_116_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_116_18, basis_im_116_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_116_19, basis_im_116_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_116_20, basis_im_116_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_116_21, basis_im_116_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_116_22, basis_im_116_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_116_23, basis_im_116_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_116_24, basis_im_116_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
