import ICO.SupportBasisProducts.Row125
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_125 (b : Fin 25) :
    basisProductRe 125 b.val = (if 125 = 103+b.val then 1 else 0) ∧
    basisProductIm 125 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_125_0, basis_im_125_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_125_1, basis_im_125_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_125_2, basis_im_125_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_125_3, basis_im_125_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_125_4, basis_im_125_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_125_5, basis_im_125_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_125_6, basis_im_125_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_125_7, basis_im_125_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_125_8, basis_im_125_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_125_9, basis_im_125_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_125_10, basis_im_125_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_125_11, basis_im_125_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_125_12, basis_im_125_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_125_13, basis_im_125_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_125_14, basis_im_125_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_125_15, basis_im_125_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_125_16, basis_im_125_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_125_17, basis_im_125_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_125_18, basis_im_125_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_125_19, basis_im_125_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_125_20, basis_im_125_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_125_21, basis_im_125_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_125_22, basis_im_125_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_125_23, basis_im_125_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_125_24, basis_im_125_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
