import ICO.SupportBasisProducts.Row55
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_55 (b : Fin 25) :
    basisProductRe 55 b.val = (if 55 = 103+b.val then 1 else 0) ∧
    basisProductIm 55 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_55_0, basis_im_55_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_55_1, basis_im_55_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_55_2, basis_im_55_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_55_3, basis_im_55_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_55_4, basis_im_55_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_55_5, basis_im_55_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_55_6, basis_im_55_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_55_7, basis_im_55_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_55_8, basis_im_55_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_55_9, basis_im_55_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_55_10, basis_im_55_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_55_11, basis_im_55_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_55_12, basis_im_55_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_55_13, basis_im_55_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_55_14, basis_im_55_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_55_15, basis_im_55_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_55_16, basis_im_55_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_55_17, basis_im_55_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_55_18, basis_im_55_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_55_19, basis_im_55_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_55_20, basis_im_55_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_55_21, basis_im_55_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_55_22, basis_im_55_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_55_23, basis_im_55_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_55_24, basis_im_55_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
