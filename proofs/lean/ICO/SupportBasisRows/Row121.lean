import ICO.SupportBasisProducts.Row121
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_121 (b : Fin 25) :
    basisProductRe 121 b.val = (if 121 = 103+b.val then 1 else 0) ∧
    basisProductIm 121 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_121_0, basis_im_121_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_121_1, basis_im_121_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_121_2, basis_im_121_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_121_3, basis_im_121_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_121_4, basis_im_121_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_121_5, basis_im_121_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_121_6, basis_im_121_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_121_7, basis_im_121_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_121_8, basis_im_121_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_121_9, basis_im_121_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_121_10, basis_im_121_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_121_11, basis_im_121_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_121_12, basis_im_121_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_121_13, basis_im_121_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_121_14, basis_im_121_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_121_15, basis_im_121_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_121_16, basis_im_121_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_121_17, basis_im_121_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_121_18, basis_im_121_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_121_19, basis_im_121_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_121_20, basis_im_121_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_121_21, basis_im_121_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_121_22, basis_im_121_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_121_23, basis_im_121_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_121_24, basis_im_121_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
