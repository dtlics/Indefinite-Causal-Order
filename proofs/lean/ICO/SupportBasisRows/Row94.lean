import ICO.SupportBasisProducts.Row94
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_94 (b : Fin 25) :
    basisProductRe 94 b.val = (if 94 = 103+b.val then 1 else 0) ∧
    basisProductIm 94 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_94_0, basis_im_94_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_94_1, basis_im_94_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_94_2, basis_im_94_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_94_3, basis_im_94_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_94_4, basis_im_94_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_94_5, basis_im_94_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_94_6, basis_im_94_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_94_7, basis_im_94_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_94_8, basis_im_94_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_94_9, basis_im_94_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_94_10, basis_im_94_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_94_11, basis_im_94_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_94_12, basis_im_94_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_94_13, basis_im_94_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_94_14, basis_im_94_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_94_15, basis_im_94_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_94_16, basis_im_94_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_94_17, basis_im_94_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_94_18, basis_im_94_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_94_19, basis_im_94_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_94_20, basis_im_94_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_94_21, basis_im_94_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_94_22, basis_im_94_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_94_23, basis_im_94_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_94_24, basis_im_94_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
