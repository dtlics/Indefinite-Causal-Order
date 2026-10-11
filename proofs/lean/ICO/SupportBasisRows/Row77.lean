import ICO.SupportBasisProducts.Row77
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_77 (b : Fin 25) :
    basisProductRe 77 b.val = (if 77 = 103+b.val then 1 else 0) ∧
    basisProductIm 77 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_77_0, basis_im_77_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_77_1, basis_im_77_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_77_2, basis_im_77_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_77_3, basis_im_77_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_77_4, basis_im_77_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_77_5, basis_im_77_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_77_6, basis_im_77_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_77_7, basis_im_77_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_77_8, basis_im_77_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_77_9, basis_im_77_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_77_10, basis_im_77_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_77_11, basis_im_77_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_77_12, basis_im_77_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_77_13, basis_im_77_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_77_14, basis_im_77_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_77_15, basis_im_77_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_77_16, basis_im_77_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_77_17, basis_im_77_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_77_18, basis_im_77_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_77_19, basis_im_77_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_77_20, basis_im_77_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_77_21, basis_im_77_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_77_22, basis_im_77_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_77_23, basis_im_77_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_77_24, basis_im_77_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
