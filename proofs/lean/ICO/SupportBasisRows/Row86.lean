import ICO.SupportBasisProducts.Row86
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_86 (b : Fin 25) :
    basisProductRe 86 b.val = (if 86 = 103+b.val then 1 else 0) ∧
    basisProductIm 86 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_86_0, basis_im_86_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_86_1, basis_im_86_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_86_2, basis_im_86_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_86_3, basis_im_86_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_86_4, basis_im_86_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_86_5, basis_im_86_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_86_6, basis_im_86_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_86_7, basis_im_86_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_86_8, basis_im_86_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_86_9, basis_im_86_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_86_10, basis_im_86_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_86_11, basis_im_86_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_86_12, basis_im_86_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_86_13, basis_im_86_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_86_14, basis_im_86_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_86_15, basis_im_86_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_86_16, basis_im_86_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_86_17, basis_im_86_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_86_18, basis_im_86_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_86_19, basis_im_86_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_86_20, basis_im_86_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_86_21, basis_im_86_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_86_22, basis_im_86_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_86_23, basis_im_86_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_86_24, basis_im_86_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
