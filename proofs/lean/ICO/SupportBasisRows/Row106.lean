import ICO.SupportBasisProducts.Row106
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_106 (b : Fin 25) :
    basisProductRe 106 b.val = (if 106 = 103+b.val then 1 else 0) ∧
    basisProductIm 106 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_106_0, basis_im_106_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_106_1, basis_im_106_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_106_2, basis_im_106_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_106_3, basis_im_106_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_106_4, basis_im_106_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_106_5, basis_im_106_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_106_6, basis_im_106_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_106_7, basis_im_106_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_106_8, basis_im_106_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_106_9, basis_im_106_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_106_10, basis_im_106_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_106_11, basis_im_106_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_106_12, basis_im_106_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_106_13, basis_im_106_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_106_14, basis_im_106_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_106_15, basis_im_106_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_106_16, basis_im_106_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_106_17, basis_im_106_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_106_18, basis_im_106_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_106_19, basis_im_106_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_106_20, basis_im_106_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_106_21, basis_im_106_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_106_22, basis_im_106_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_106_23, basis_im_106_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_106_24, basis_im_106_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
