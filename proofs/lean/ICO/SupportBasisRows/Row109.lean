import ICO.SupportBasisProducts.Row109
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_109 (b : Fin 25) :
    basisProductRe 109 b.val = (if 109 = 103+b.val then 1 else 0) ∧
    basisProductIm 109 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_109_0, basis_im_109_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_109_1, basis_im_109_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_109_2, basis_im_109_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_109_3, basis_im_109_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_109_4, basis_im_109_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_109_5, basis_im_109_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_109_6, basis_im_109_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_109_7, basis_im_109_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_109_8, basis_im_109_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_109_9, basis_im_109_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_109_10, basis_im_109_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_109_11, basis_im_109_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_109_12, basis_im_109_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_109_13, basis_im_109_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_109_14, basis_im_109_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_109_15, basis_im_109_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_109_16, basis_im_109_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_109_17, basis_im_109_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_109_18, basis_im_109_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_109_19, basis_im_109_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_109_20, basis_im_109_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_109_21, basis_im_109_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_109_22, basis_im_109_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_109_23, basis_im_109_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_109_24, basis_im_109_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
