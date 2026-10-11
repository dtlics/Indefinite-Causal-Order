import ICO.SupportBasisProducts.Row48
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_48 (b : Fin 25) :
    basisProductRe 48 b.val = (if 48 = 103+b.val then 1 else 0) ∧
    basisProductIm 48 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_48_0, basis_im_48_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_48_1, basis_im_48_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_48_2, basis_im_48_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_48_3, basis_im_48_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_48_4, basis_im_48_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_48_5, basis_im_48_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_48_6, basis_im_48_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_48_7, basis_im_48_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_48_8, basis_im_48_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_48_9, basis_im_48_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_48_10, basis_im_48_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_48_11, basis_im_48_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_48_12, basis_im_48_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_48_13, basis_im_48_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_48_14, basis_im_48_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_48_15, basis_im_48_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_48_16, basis_im_48_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_48_17, basis_im_48_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_48_18, basis_im_48_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_48_19, basis_im_48_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_48_20, basis_im_48_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_48_21, basis_im_48_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_48_22, basis_im_48_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_48_23, basis_im_48_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_48_24, basis_im_48_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
