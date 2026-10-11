import ICO.SupportBasisProducts.Row45
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_45 (b : Fin 25) :
    basisProductRe 45 b.val = (if 45 = 103+b.val then 1 else 0) ∧
    basisProductIm 45 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_45_0, basis_im_45_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_45_1, basis_im_45_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_45_2, basis_im_45_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_45_3, basis_im_45_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_45_4, basis_im_45_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_45_5, basis_im_45_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_45_6, basis_im_45_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_45_7, basis_im_45_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_45_8, basis_im_45_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_45_9, basis_im_45_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_45_10, basis_im_45_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_45_11, basis_im_45_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_45_12, basis_im_45_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_45_13, basis_im_45_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_45_14, basis_im_45_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_45_15, basis_im_45_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_45_16, basis_im_45_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_45_17, basis_im_45_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_45_18, basis_im_45_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_45_19, basis_im_45_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_45_20, basis_im_45_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_45_21, basis_im_45_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_45_22, basis_im_45_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_45_23, basis_im_45_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_45_24, basis_im_45_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
