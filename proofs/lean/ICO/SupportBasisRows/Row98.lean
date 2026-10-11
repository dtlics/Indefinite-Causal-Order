import ICO.SupportBasisProducts.Row98
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_98 (b : Fin 25) :
    basisProductRe 98 b.val = (if 98 = 103+b.val then 1 else 0) ∧
    basisProductIm 98 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_98_0, basis_im_98_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_98_1, basis_im_98_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_98_2, basis_im_98_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_98_3, basis_im_98_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_98_4, basis_im_98_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_98_5, basis_im_98_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_98_6, basis_im_98_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_98_7, basis_im_98_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_98_8, basis_im_98_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_98_9, basis_im_98_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_98_10, basis_im_98_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_98_11, basis_im_98_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_98_12, basis_im_98_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_98_13, basis_im_98_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_98_14, basis_im_98_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_98_15, basis_im_98_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_98_16, basis_im_98_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_98_17, basis_im_98_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_98_18, basis_im_98_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_98_19, basis_im_98_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_98_20, basis_im_98_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_98_21, basis_im_98_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_98_22, basis_im_98_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_98_23, basis_im_98_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_98_24, basis_im_98_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
