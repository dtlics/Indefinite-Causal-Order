import ICO.SupportBasisProducts.Row74
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_74 (b : Fin 25) :
    basisProductRe 74 b.val = (if 74 = 103+b.val then 1 else 0) ∧
    basisProductIm 74 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_74_0, basis_im_74_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_74_1, basis_im_74_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_74_2, basis_im_74_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_74_3, basis_im_74_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_74_4, basis_im_74_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_74_5, basis_im_74_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_74_6, basis_im_74_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_74_7, basis_im_74_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_74_8, basis_im_74_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_74_9, basis_im_74_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_74_10, basis_im_74_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_74_11, basis_im_74_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_74_12, basis_im_74_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_74_13, basis_im_74_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_74_14, basis_im_74_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_74_15, basis_im_74_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_74_16, basis_im_74_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_74_17, basis_im_74_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_74_18, basis_im_74_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_74_19, basis_im_74_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_74_20, basis_im_74_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_74_21, basis_im_74_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_74_22, basis_im_74_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_74_23, basis_im_74_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_74_24, basis_im_74_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
