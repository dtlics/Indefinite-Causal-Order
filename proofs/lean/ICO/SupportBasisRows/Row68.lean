import ICO.SupportBasisProducts.Row68
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_68 (b : Fin 25) :
    basisProductRe 68 b.val = (if 68 = 103+b.val then 1 else 0) ∧
    basisProductIm 68 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_68_0, basis_im_68_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_68_1, basis_im_68_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_68_2, basis_im_68_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_68_3, basis_im_68_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_68_4, basis_im_68_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_68_5, basis_im_68_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_68_6, basis_im_68_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_68_7, basis_im_68_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_68_8, basis_im_68_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_68_9, basis_im_68_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_68_10, basis_im_68_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_68_11, basis_im_68_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_68_12, basis_im_68_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_68_13, basis_im_68_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_68_14, basis_im_68_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_68_15, basis_im_68_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_68_16, basis_im_68_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_68_17, basis_im_68_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_68_18, basis_im_68_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_68_19, basis_im_68_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_68_20, basis_im_68_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_68_21, basis_im_68_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_68_22, basis_im_68_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_68_23, basis_im_68_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_68_24, basis_im_68_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
