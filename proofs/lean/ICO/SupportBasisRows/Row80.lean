import ICO.SupportBasisProducts.Row80
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_80 (b : Fin 25) :
    basisProductRe 80 b.val = (if 80 = 103+b.val then 1 else 0) ∧
    basisProductIm 80 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_80_0, basis_im_80_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_80_1, basis_im_80_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_80_2, basis_im_80_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_80_3, basis_im_80_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_80_4, basis_im_80_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_80_5, basis_im_80_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_80_6, basis_im_80_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_80_7, basis_im_80_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_80_8, basis_im_80_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_80_9, basis_im_80_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_80_10, basis_im_80_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_80_11, basis_im_80_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_80_12, basis_im_80_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_80_13, basis_im_80_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_80_14, basis_im_80_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_80_15, basis_im_80_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_80_16, basis_im_80_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_80_17, basis_im_80_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_80_18, basis_im_80_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_80_19, basis_im_80_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_80_20, basis_im_80_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_80_21, basis_im_80_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_80_22, basis_im_80_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_80_23, basis_im_80_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_80_24, basis_im_80_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
