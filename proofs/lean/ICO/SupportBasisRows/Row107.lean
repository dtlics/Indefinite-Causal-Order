import ICO.SupportBasisProducts.Row107
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_107 (b : Fin 25) :
    basisProductRe 107 b.val = (if 107 = 103+b.val then 1 else 0) ∧
    basisProductIm 107 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_107_0, basis_im_107_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_107_1, basis_im_107_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_107_2, basis_im_107_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_107_3, basis_im_107_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_107_4, basis_im_107_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_107_5, basis_im_107_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_107_6, basis_im_107_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_107_7, basis_im_107_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_107_8, basis_im_107_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_107_9, basis_im_107_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_107_10, basis_im_107_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_107_11, basis_im_107_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_107_12, basis_im_107_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_107_13, basis_im_107_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_107_14, basis_im_107_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_107_15, basis_im_107_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_107_16, basis_im_107_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_107_17, basis_im_107_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_107_18, basis_im_107_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_107_19, basis_im_107_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_107_20, basis_im_107_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_107_21, basis_im_107_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_107_22, basis_im_107_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_107_23, basis_im_107_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_107_24, basis_im_107_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
