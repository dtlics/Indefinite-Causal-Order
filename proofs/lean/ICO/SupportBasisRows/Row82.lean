import ICO.SupportBasisProducts.Row82
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_82 (b : Fin 25) :
    basisProductRe 82 b.val = (if 82 = 103+b.val then 1 else 0) ∧
    basisProductIm 82 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_82_0, basis_im_82_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_82_1, basis_im_82_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_82_2, basis_im_82_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_82_3, basis_im_82_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_82_4, basis_im_82_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_82_5, basis_im_82_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_82_6, basis_im_82_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_82_7, basis_im_82_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_82_8, basis_im_82_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_82_9, basis_im_82_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_82_10, basis_im_82_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_82_11, basis_im_82_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_82_12, basis_im_82_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_82_13, basis_im_82_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_82_14, basis_im_82_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_82_15, basis_im_82_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_82_16, basis_im_82_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_82_17, basis_im_82_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_82_18, basis_im_82_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_82_19, basis_im_82_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_82_20, basis_im_82_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_82_21, basis_im_82_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_82_22, basis_im_82_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_82_23, basis_im_82_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_82_24, basis_im_82_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
