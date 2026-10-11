import ICO.SupportBasisProducts.Row38
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_38 (b : Fin 25) :
    basisProductRe 38 b.val = (if 38 = 103+b.val then 1 else 0) ∧
    basisProductIm 38 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_38_0, basis_im_38_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_38_1, basis_im_38_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_38_2, basis_im_38_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_38_3, basis_im_38_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_38_4, basis_im_38_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_38_5, basis_im_38_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_38_6, basis_im_38_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_38_7, basis_im_38_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_38_8, basis_im_38_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_38_9, basis_im_38_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_38_10, basis_im_38_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_38_11, basis_im_38_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_38_12, basis_im_38_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_38_13, basis_im_38_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_38_14, basis_im_38_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_38_15, basis_im_38_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_38_16, basis_im_38_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_38_17, basis_im_38_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_38_18, basis_im_38_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_38_19, basis_im_38_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_38_20, basis_im_38_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_38_21, basis_im_38_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_38_22, basis_im_38_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_38_23, basis_im_38_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_38_24, basis_im_38_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
