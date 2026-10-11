import ICO.SupportBasisProducts.Row25
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_25 (b : Fin 25) :
    basisProductRe 25 b.val = (if 25 = 103+b.val then 1 else 0) ∧
    basisProductIm 25 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_25_0, basis_im_25_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_25_1, basis_im_25_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_25_2, basis_im_25_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_25_3, basis_im_25_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_25_4, basis_im_25_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_25_5, basis_im_25_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_25_6, basis_im_25_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_25_7, basis_im_25_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_25_8, basis_im_25_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_25_9, basis_im_25_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_25_10, basis_im_25_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_25_11, basis_im_25_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_25_12, basis_im_25_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_25_13, basis_im_25_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_25_14, basis_im_25_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_25_15, basis_im_25_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_25_16, basis_im_25_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_25_17, basis_im_25_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_25_18, basis_im_25_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_25_19, basis_im_25_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_25_20, basis_im_25_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_25_21, basis_im_25_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_25_22, basis_im_25_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_25_23, basis_im_25_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_25_24, basis_im_25_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
