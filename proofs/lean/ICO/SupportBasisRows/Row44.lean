import ICO.SupportBasisProducts.Row44
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_44 (b : Fin 25) :
    basisProductRe 44 b.val = (if 44 = 103+b.val then 1 else 0) ∧
    basisProductIm 44 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_44_0, basis_im_44_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_44_1, basis_im_44_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_44_2, basis_im_44_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_44_3, basis_im_44_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_44_4, basis_im_44_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_44_5, basis_im_44_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_44_6, basis_im_44_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_44_7, basis_im_44_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_44_8, basis_im_44_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_44_9, basis_im_44_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_44_10, basis_im_44_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_44_11, basis_im_44_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_44_12, basis_im_44_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_44_13, basis_im_44_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_44_14, basis_im_44_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_44_15, basis_im_44_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_44_16, basis_im_44_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_44_17, basis_im_44_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_44_18, basis_im_44_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_44_19, basis_im_44_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_44_20, basis_im_44_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_44_21, basis_im_44_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_44_22, basis_im_44_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_44_23, basis_im_44_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_44_24, basis_im_44_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
