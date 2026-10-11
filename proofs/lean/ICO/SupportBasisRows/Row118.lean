import ICO.SupportBasisProducts.Row118
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_118 (b : Fin 25) :
    basisProductRe 118 b.val = (if 118 = 103+b.val then 1 else 0) ∧
    basisProductIm 118 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_118_0, basis_im_118_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_118_1, basis_im_118_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_118_2, basis_im_118_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_118_3, basis_im_118_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_118_4, basis_im_118_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_118_5, basis_im_118_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_118_6, basis_im_118_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_118_7, basis_im_118_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_118_8, basis_im_118_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_118_9, basis_im_118_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_118_10, basis_im_118_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_118_11, basis_im_118_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_118_12, basis_im_118_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_118_13, basis_im_118_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_118_14, basis_im_118_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_118_15, basis_im_118_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_118_16, basis_im_118_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_118_17, basis_im_118_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_118_18, basis_im_118_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_118_19, basis_im_118_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_118_20, basis_im_118_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_118_21, basis_im_118_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_118_22, basis_im_118_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_118_23, basis_im_118_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_118_24, basis_im_118_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
