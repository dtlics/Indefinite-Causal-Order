import ICO.SupportBasisProducts.Row85
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_85 (b : Fin 25) :
    basisProductRe 85 b.val = (if 85 = 103+b.val then 1 else 0) ∧
    basisProductIm 85 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_85_0, basis_im_85_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_85_1, basis_im_85_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_85_2, basis_im_85_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_85_3, basis_im_85_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_85_4, basis_im_85_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_85_5, basis_im_85_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_85_6, basis_im_85_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_85_7, basis_im_85_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_85_8, basis_im_85_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_85_9, basis_im_85_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_85_10, basis_im_85_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_85_11, basis_im_85_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_85_12, basis_im_85_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_85_13, basis_im_85_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_85_14, basis_im_85_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_85_15, basis_im_85_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_85_16, basis_im_85_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_85_17, basis_im_85_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_85_18, basis_im_85_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_85_19, basis_im_85_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_85_20, basis_im_85_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_85_21, basis_im_85_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_85_22, basis_im_85_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_85_23, basis_im_85_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_85_24, basis_im_85_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
