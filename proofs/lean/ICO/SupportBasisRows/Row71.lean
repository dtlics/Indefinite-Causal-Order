import ICO.SupportBasisProducts.Row71
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_71 (b : Fin 25) :
    basisProductRe 71 b.val = (if 71 = 103+b.val then 1 else 0) ∧
    basisProductIm 71 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_71_0, basis_im_71_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_71_1, basis_im_71_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_71_2, basis_im_71_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_71_3, basis_im_71_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_71_4, basis_im_71_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_71_5, basis_im_71_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_71_6, basis_im_71_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_71_7, basis_im_71_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_71_8, basis_im_71_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_71_9, basis_im_71_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_71_10, basis_im_71_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_71_11, basis_im_71_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_71_12, basis_im_71_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_71_13, basis_im_71_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_71_14, basis_im_71_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_71_15, basis_im_71_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_71_16, basis_im_71_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_71_17, basis_im_71_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_71_18, basis_im_71_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_71_19, basis_im_71_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_71_20, basis_im_71_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_71_21, basis_im_71_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_71_22, basis_im_71_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_71_23, basis_im_71_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_71_24, basis_im_71_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
