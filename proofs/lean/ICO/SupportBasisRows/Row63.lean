import ICO.SupportBasisProducts.Row63
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_63 (b : Fin 25) :
    basisProductRe 63 b.val = (if 63 = 103+b.val then 1 else 0) ∧
    basisProductIm 63 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_63_0, basis_im_63_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_63_1, basis_im_63_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_63_2, basis_im_63_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_63_3, basis_im_63_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_63_4, basis_im_63_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_63_5, basis_im_63_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_63_6, basis_im_63_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_63_7, basis_im_63_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_63_8, basis_im_63_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_63_9, basis_im_63_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_63_10, basis_im_63_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_63_11, basis_im_63_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_63_12, basis_im_63_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_63_13, basis_im_63_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_63_14, basis_im_63_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_63_15, basis_im_63_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_63_16, basis_im_63_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_63_17, basis_im_63_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_63_18, basis_im_63_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_63_19, basis_im_63_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_63_20, basis_im_63_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_63_21, basis_im_63_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_63_22, basis_im_63_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_63_23, basis_im_63_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_63_24, basis_im_63_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
