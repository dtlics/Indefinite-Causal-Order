import ICO.SupportBasisProducts.Row101
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_101 (b : Fin 25) :
    basisProductRe 101 b.val = (if 101 = 103+b.val then 1 else 0) ∧
    basisProductIm 101 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_101_0, basis_im_101_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_101_1, basis_im_101_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_101_2, basis_im_101_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_101_3, basis_im_101_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_101_4, basis_im_101_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_101_5, basis_im_101_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_101_6, basis_im_101_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_101_7, basis_im_101_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_101_8, basis_im_101_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_101_9, basis_im_101_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_101_10, basis_im_101_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_101_11, basis_im_101_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_101_12, basis_im_101_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_101_13, basis_im_101_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_101_14, basis_im_101_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_101_15, basis_im_101_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_101_16, basis_im_101_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_101_17, basis_im_101_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_101_18, basis_im_101_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_101_19, basis_im_101_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_101_20, basis_im_101_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_101_21, basis_im_101_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_101_22, basis_im_101_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_101_23, basis_im_101_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_101_24, basis_im_101_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
