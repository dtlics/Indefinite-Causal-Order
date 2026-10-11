import ICO.SupportBasisProducts.Row20
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_20 (b : Fin 25) :
    basisProductRe 20 b.val = (if 20 = 103+b.val then 1 else 0) ∧
    basisProductIm 20 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_20_0, basis_im_20_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_20_1, basis_im_20_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_20_2, basis_im_20_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_20_3, basis_im_20_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_20_4, basis_im_20_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_20_5, basis_im_20_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_20_6, basis_im_20_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_20_7, basis_im_20_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_20_8, basis_im_20_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_20_9, basis_im_20_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_20_10, basis_im_20_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_20_11, basis_im_20_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_20_12, basis_im_20_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_20_13, basis_im_20_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_20_14, basis_im_20_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_20_15, basis_im_20_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_20_16, basis_im_20_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_20_17, basis_im_20_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_20_18, basis_im_20_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_20_19, basis_im_20_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_20_20, basis_im_20_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_20_21, basis_im_20_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_20_22, basis_im_20_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_20_23, basis_im_20_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_20_24, basis_im_20_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
