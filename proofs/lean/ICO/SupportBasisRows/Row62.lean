import ICO.SupportBasisProducts.Row62
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_62 (b : Fin 25) :
    basisProductRe 62 b.val = (if 62 = 103+b.val then 1 else 0) ∧
    basisProductIm 62 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_62_0, basis_im_62_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_62_1, basis_im_62_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_62_2, basis_im_62_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_62_3, basis_im_62_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_62_4, basis_im_62_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_62_5, basis_im_62_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_62_6, basis_im_62_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_62_7, basis_im_62_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_62_8, basis_im_62_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_62_9, basis_im_62_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_62_10, basis_im_62_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_62_11, basis_im_62_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_62_12, basis_im_62_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_62_13, basis_im_62_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_62_14, basis_im_62_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_62_15, basis_im_62_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_62_16, basis_im_62_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_62_17, basis_im_62_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_62_18, basis_im_62_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_62_19, basis_im_62_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_62_20, basis_im_62_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_62_21, basis_im_62_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_62_22, basis_im_62_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_62_23, basis_im_62_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_62_24, basis_im_62_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
