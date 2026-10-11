import ICO.SupportBasisProducts.Row110
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_110 (b : Fin 25) :
    basisProductRe 110 b.val = (if 110 = 103+b.val then 1 else 0) ∧
    basisProductIm 110 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_110_0, basis_im_110_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_110_1, basis_im_110_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_110_2, basis_im_110_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_110_3, basis_im_110_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_110_4, basis_im_110_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_110_5, basis_im_110_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_110_6, basis_im_110_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_110_7, basis_im_110_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_110_8, basis_im_110_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_110_9, basis_im_110_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_110_10, basis_im_110_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_110_11, basis_im_110_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_110_12, basis_im_110_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_110_13, basis_im_110_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_110_14, basis_im_110_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_110_15, basis_im_110_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_110_16, basis_im_110_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_110_17, basis_im_110_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_110_18, basis_im_110_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_110_19, basis_im_110_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_110_20, basis_im_110_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_110_21, basis_im_110_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_110_22, basis_im_110_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_110_23, basis_im_110_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_110_24, basis_im_110_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
