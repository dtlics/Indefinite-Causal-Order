import ICO.SupportBasisProducts.Row89
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_89 (b : Fin 25) :
    basisProductRe 89 b.val = (if 89 = 103+b.val then 1 else 0) ∧
    basisProductIm 89 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_89_0, basis_im_89_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_89_1, basis_im_89_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_89_2, basis_im_89_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_89_3, basis_im_89_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_89_4, basis_im_89_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_89_5, basis_im_89_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_89_6, basis_im_89_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_89_7, basis_im_89_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_89_8, basis_im_89_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_89_9, basis_im_89_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_89_10, basis_im_89_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_89_11, basis_im_89_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_89_12, basis_im_89_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_89_13, basis_im_89_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_89_14, basis_im_89_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_89_15, basis_im_89_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_89_16, basis_im_89_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_89_17, basis_im_89_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_89_18, basis_im_89_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_89_19, basis_im_89_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_89_20, basis_im_89_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_89_21, basis_im_89_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_89_22, basis_im_89_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_89_23, basis_im_89_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_89_24, basis_im_89_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
