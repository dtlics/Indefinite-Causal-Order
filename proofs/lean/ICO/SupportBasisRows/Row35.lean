import ICO.SupportBasisProducts.Row35
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_35 (b : Fin 25) :
    basisProductRe 35 b.val = (if 35 = 103+b.val then 1 else 0) ∧
    basisProductIm 35 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_35_0, basis_im_35_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_35_1, basis_im_35_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_35_2, basis_im_35_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_35_3, basis_im_35_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_35_4, basis_im_35_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_35_5, basis_im_35_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_35_6, basis_im_35_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_35_7, basis_im_35_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_35_8, basis_im_35_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_35_9, basis_im_35_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_35_10, basis_im_35_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_35_11, basis_im_35_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_35_12, basis_im_35_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_35_13, basis_im_35_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_35_14, basis_im_35_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_35_15, basis_im_35_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_35_16, basis_im_35_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_35_17, basis_im_35_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_35_18, basis_im_35_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_35_19, basis_im_35_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_35_20, basis_im_35_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_35_21, basis_im_35_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_35_22, basis_im_35_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_35_23, basis_im_35_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_35_24, basis_im_35_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
