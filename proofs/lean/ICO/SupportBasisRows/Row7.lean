import ICO.SupportBasisProducts.Row7
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_7 (b : Fin 25) :
    basisProductRe 7 b.val = (if 7 = 103+b.val then 1 else 0) ∧
    basisProductIm 7 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_7_0, basis_im_7_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_7_1, basis_im_7_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_7_2, basis_im_7_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_7_3, basis_im_7_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_7_4, basis_im_7_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_7_5, basis_im_7_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_7_6, basis_im_7_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_7_7, basis_im_7_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_7_8, basis_im_7_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_7_9, basis_im_7_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_7_10, basis_im_7_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_7_11, basis_im_7_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_7_12, basis_im_7_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_7_13, basis_im_7_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_7_14, basis_im_7_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_7_15, basis_im_7_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_7_16, basis_im_7_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_7_17, basis_im_7_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_7_18, basis_im_7_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_7_19, basis_im_7_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_7_20, basis_im_7_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_7_21, basis_im_7_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_7_22, basis_im_7_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_7_23, basis_im_7_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_7_24, basis_im_7_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
