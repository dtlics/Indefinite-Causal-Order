import ICO.SupportBasisProducts.Row126
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_126 (b : Fin 25) :
    basisProductRe 126 b.val = (if 126 = 103+b.val then 1 else 0) ∧
    basisProductIm 126 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_126_0, basis_im_126_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_126_1, basis_im_126_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_126_2, basis_im_126_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_126_3, basis_im_126_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_126_4, basis_im_126_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_126_5, basis_im_126_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_126_6, basis_im_126_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_126_7, basis_im_126_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_126_8, basis_im_126_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_126_9, basis_im_126_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_126_10, basis_im_126_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_126_11, basis_im_126_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_126_12, basis_im_126_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_126_13, basis_im_126_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_126_14, basis_im_126_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_126_15, basis_im_126_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_126_16, basis_im_126_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_126_17, basis_im_126_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_126_18, basis_im_126_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_126_19, basis_im_126_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_126_20, basis_im_126_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_126_21, basis_im_126_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_126_22, basis_im_126_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_126_23, basis_im_126_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_126_24, basis_im_126_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
