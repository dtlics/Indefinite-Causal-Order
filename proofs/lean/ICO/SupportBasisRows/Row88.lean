import ICO.SupportBasisProducts.Row88
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_88 (b : Fin 25) :
    basisProductRe 88 b.val = (if 88 = 103+b.val then 1 else 0) ∧
    basisProductIm 88 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_88_0, basis_im_88_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_88_1, basis_im_88_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_88_2, basis_im_88_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_88_3, basis_im_88_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_88_4, basis_im_88_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_88_5, basis_im_88_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_88_6, basis_im_88_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_88_7, basis_im_88_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_88_8, basis_im_88_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_88_9, basis_im_88_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_88_10, basis_im_88_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_88_11, basis_im_88_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_88_12, basis_im_88_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_88_13, basis_im_88_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_88_14, basis_im_88_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_88_15, basis_im_88_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_88_16, basis_im_88_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_88_17, basis_im_88_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_88_18, basis_im_88_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_88_19, basis_im_88_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_88_20, basis_im_88_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_88_21, basis_im_88_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_88_22, basis_im_88_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_88_23, basis_im_88_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_88_24, basis_im_88_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
