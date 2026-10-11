import ICO.SupportBasisProducts.Row12
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_12 (b : Fin 25) :
    basisProductRe 12 b.val = (if 12 = 103+b.val then 1 else 0) ∧
    basisProductIm 12 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_12_0, basis_im_12_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_12_1, basis_im_12_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_12_2, basis_im_12_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_12_3, basis_im_12_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_12_4, basis_im_12_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_12_5, basis_im_12_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_12_6, basis_im_12_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_12_7, basis_im_12_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_12_8, basis_im_12_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_12_9, basis_im_12_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_12_10, basis_im_12_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_12_11, basis_im_12_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_12_12, basis_im_12_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_12_13, basis_im_12_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_12_14, basis_im_12_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_12_15, basis_im_12_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_12_16, basis_im_12_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_12_17, basis_im_12_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_12_18, basis_im_12_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_12_19, basis_im_12_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_12_20, basis_im_12_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_12_21, basis_im_12_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_12_22, basis_im_12_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_12_23, basis_im_12_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_12_24, basis_im_12_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
