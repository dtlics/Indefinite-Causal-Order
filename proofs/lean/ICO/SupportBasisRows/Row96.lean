import ICO.SupportBasisProducts.Row96
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_96 (b : Fin 25) :
    basisProductRe 96 b.val = (if 96 = 103+b.val then 1 else 0) ∧
    basisProductIm 96 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_96_0, basis_im_96_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_96_1, basis_im_96_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_96_2, basis_im_96_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_96_3, basis_im_96_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_96_4, basis_im_96_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_96_5, basis_im_96_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_96_6, basis_im_96_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_96_7, basis_im_96_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_96_8, basis_im_96_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_96_9, basis_im_96_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_96_10, basis_im_96_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_96_11, basis_im_96_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_96_12, basis_im_96_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_96_13, basis_im_96_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_96_14, basis_im_96_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_96_15, basis_im_96_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_96_16, basis_im_96_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_96_17, basis_im_96_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_96_18, basis_im_96_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_96_19, basis_im_96_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_96_20, basis_im_96_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_96_21, basis_im_96_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_96_22, basis_im_96_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_96_23, basis_im_96_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_96_24, basis_im_96_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
