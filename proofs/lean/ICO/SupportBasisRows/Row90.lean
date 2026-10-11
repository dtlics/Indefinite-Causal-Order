import ICO.SupportBasisProducts.Row90
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_90 (b : Fin 25) :
    basisProductRe 90 b.val = (if 90 = 103+b.val then 1 else 0) ∧
    basisProductIm 90 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_90_0, basis_im_90_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_90_1, basis_im_90_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_90_2, basis_im_90_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_90_3, basis_im_90_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_90_4, basis_im_90_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_90_5, basis_im_90_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_90_6, basis_im_90_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_90_7, basis_im_90_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_90_8, basis_im_90_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_90_9, basis_im_90_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_90_10, basis_im_90_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_90_11, basis_im_90_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_90_12, basis_im_90_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_90_13, basis_im_90_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_90_14, basis_im_90_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_90_15, basis_im_90_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_90_16, basis_im_90_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_90_17, basis_im_90_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_90_18, basis_im_90_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_90_19, basis_im_90_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_90_20, basis_im_90_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_90_21, basis_im_90_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_90_22, basis_im_90_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_90_23, basis_im_90_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_90_24, basis_im_90_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
