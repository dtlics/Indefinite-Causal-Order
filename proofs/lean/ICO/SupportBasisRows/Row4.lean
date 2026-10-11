import ICO.SupportBasisProducts.Row4
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_4 (b : Fin 25) :
    basisProductRe 4 b.val = (if 4 = 103+b.val then 1 else 0) ∧
    basisProductIm 4 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_4_0, basis_im_4_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_4_1, basis_im_4_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_4_2, basis_im_4_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_4_3, basis_im_4_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_4_4, basis_im_4_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_4_5, basis_im_4_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_4_6, basis_im_4_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_4_7, basis_im_4_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_4_8, basis_im_4_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_4_9, basis_im_4_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_4_10, basis_im_4_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_4_11, basis_im_4_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_4_12, basis_im_4_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_4_13, basis_im_4_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_4_14, basis_im_4_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_4_15, basis_im_4_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_4_16, basis_im_4_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_4_17, basis_im_4_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_4_18, basis_im_4_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_4_19, basis_im_4_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_4_20, basis_im_4_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_4_21, basis_im_4_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_4_22, basis_im_4_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_4_23, basis_im_4_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_4_24, basis_im_4_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
