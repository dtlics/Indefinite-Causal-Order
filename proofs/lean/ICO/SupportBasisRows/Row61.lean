import ICO.SupportBasisProducts.Row61
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_61 (b : Fin 25) :
    basisProductRe 61 b.val = (if 61 = 103+b.val then 1 else 0) ∧
    basisProductIm 61 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_61_0, basis_im_61_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_61_1, basis_im_61_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_61_2, basis_im_61_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_61_3, basis_im_61_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_61_4, basis_im_61_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_61_5, basis_im_61_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_61_6, basis_im_61_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_61_7, basis_im_61_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_61_8, basis_im_61_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_61_9, basis_im_61_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_61_10, basis_im_61_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_61_11, basis_im_61_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_61_12, basis_im_61_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_61_13, basis_im_61_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_61_14, basis_im_61_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_61_15, basis_im_61_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_61_16, basis_im_61_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_61_17, basis_im_61_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_61_18, basis_im_61_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_61_19, basis_im_61_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_61_20, basis_im_61_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_61_21, basis_im_61_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_61_22, basis_im_61_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_61_23, basis_im_61_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_61_24, basis_im_61_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
