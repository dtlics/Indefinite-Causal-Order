import ICO.SupportBasisProducts.Row112
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_112 (b : Fin 25) :
    basisProductRe 112 b.val = (if 112 = 103+b.val then 1 else 0) ∧
    basisProductIm 112 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_112_0, basis_im_112_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_112_1, basis_im_112_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_112_2, basis_im_112_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_112_3, basis_im_112_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_112_4, basis_im_112_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_112_5, basis_im_112_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_112_6, basis_im_112_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_112_7, basis_im_112_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_112_8, basis_im_112_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_112_9, basis_im_112_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_112_10, basis_im_112_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_112_11, basis_im_112_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_112_12, basis_im_112_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_112_13, basis_im_112_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_112_14, basis_im_112_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_112_15, basis_im_112_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_112_16, basis_im_112_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_112_17, basis_im_112_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_112_18, basis_im_112_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_112_19, basis_im_112_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_112_20, basis_im_112_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_112_21, basis_im_112_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_112_22, basis_im_112_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_112_23, basis_im_112_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_112_24, basis_im_112_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
