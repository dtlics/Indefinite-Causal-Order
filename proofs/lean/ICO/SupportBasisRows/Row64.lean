import ICO.SupportBasisProducts.Row64
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_64 (b : Fin 25) :
    basisProductRe 64 b.val = (if 64 = 103+b.val then 1 else 0) ∧
    basisProductIm 64 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_64_0, basis_im_64_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_64_1, basis_im_64_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_64_2, basis_im_64_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_64_3, basis_im_64_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_64_4, basis_im_64_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_64_5, basis_im_64_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_64_6, basis_im_64_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_64_7, basis_im_64_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_64_8, basis_im_64_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_64_9, basis_im_64_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_64_10, basis_im_64_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_64_11, basis_im_64_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_64_12, basis_im_64_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_64_13, basis_im_64_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_64_14, basis_im_64_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_64_15, basis_im_64_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_64_16, basis_im_64_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_64_17, basis_im_64_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_64_18, basis_im_64_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_64_19, basis_im_64_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_64_20, basis_im_64_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_64_21, basis_im_64_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_64_22, basis_im_64_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_64_23, basis_im_64_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_64_24, basis_im_64_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
