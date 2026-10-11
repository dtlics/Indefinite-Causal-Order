import ICO.SupportBasisProducts.Row97
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_97 (b : Fin 25) :
    basisProductRe 97 b.val = (if 97 = 103+b.val then 1 else 0) ∧
    basisProductIm 97 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_97_0, basis_im_97_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_97_1, basis_im_97_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_97_2, basis_im_97_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_97_3, basis_im_97_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_97_4, basis_im_97_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_97_5, basis_im_97_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_97_6, basis_im_97_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_97_7, basis_im_97_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_97_8, basis_im_97_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_97_9, basis_im_97_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_97_10, basis_im_97_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_97_11, basis_im_97_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_97_12, basis_im_97_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_97_13, basis_im_97_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_97_14, basis_im_97_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_97_15, basis_im_97_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_97_16, basis_im_97_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_97_17, basis_im_97_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_97_18, basis_im_97_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_97_19, basis_im_97_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_97_20, basis_im_97_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_97_21, basis_im_97_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_97_22, basis_im_97_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_97_23, basis_im_97_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_97_24, basis_im_97_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
