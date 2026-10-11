import ICO.SupportBasisProducts.Row51
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_51 (b : Fin 25) :
    basisProductRe 51 b.val = (if 51 = 103+b.val then 1 else 0) ∧
    basisProductIm 51 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_51_0, basis_im_51_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_51_1, basis_im_51_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_51_2, basis_im_51_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_51_3, basis_im_51_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_51_4, basis_im_51_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_51_5, basis_im_51_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_51_6, basis_im_51_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_51_7, basis_im_51_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_51_8, basis_im_51_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_51_9, basis_im_51_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_51_10, basis_im_51_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_51_11, basis_im_51_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_51_12, basis_im_51_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_51_13, basis_im_51_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_51_14, basis_im_51_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_51_15, basis_im_51_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_51_16, basis_im_51_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_51_17, basis_im_51_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_51_18, basis_im_51_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_51_19, basis_im_51_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_51_20, basis_im_51_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_51_21, basis_im_51_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_51_22, basis_im_51_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_51_23, basis_im_51_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_51_24, basis_im_51_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
