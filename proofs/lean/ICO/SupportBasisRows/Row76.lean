import ICO.SupportBasisProducts.Row76
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_76 (b : Fin 25) :
    basisProductRe 76 b.val = (if 76 = 103+b.val then 1 else 0) ∧
    basisProductIm 76 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_76_0, basis_im_76_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_76_1, basis_im_76_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_76_2, basis_im_76_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_76_3, basis_im_76_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_76_4, basis_im_76_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_76_5, basis_im_76_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_76_6, basis_im_76_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_76_7, basis_im_76_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_76_8, basis_im_76_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_76_9, basis_im_76_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_76_10, basis_im_76_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_76_11, basis_im_76_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_76_12, basis_im_76_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_76_13, basis_im_76_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_76_14, basis_im_76_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_76_15, basis_im_76_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_76_16, basis_im_76_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_76_17, basis_im_76_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_76_18, basis_im_76_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_76_19, basis_im_76_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_76_20, basis_im_76_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_76_21, basis_im_76_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_76_22, basis_im_76_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_76_23, basis_im_76_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_76_24, basis_im_76_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
