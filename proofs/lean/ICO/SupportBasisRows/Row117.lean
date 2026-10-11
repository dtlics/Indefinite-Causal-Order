import ICO.SupportBasisProducts.Row117
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_117 (b : Fin 25) :
    basisProductRe 117 b.val = (if 117 = 103+b.val then 1 else 0) ∧
    basisProductIm 117 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_117_0, basis_im_117_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_117_1, basis_im_117_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_117_2, basis_im_117_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_117_3, basis_im_117_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_117_4, basis_im_117_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_117_5, basis_im_117_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_117_6, basis_im_117_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_117_7, basis_im_117_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_117_8, basis_im_117_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_117_9, basis_im_117_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_117_10, basis_im_117_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_117_11, basis_im_117_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_117_12, basis_im_117_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_117_13, basis_im_117_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_117_14, basis_im_117_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_117_15, basis_im_117_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_117_16, basis_im_117_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_117_17, basis_im_117_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_117_18, basis_im_117_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_117_19, basis_im_117_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_117_20, basis_im_117_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_117_21, basis_im_117_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_117_22, basis_im_117_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_117_23, basis_im_117_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_117_24, basis_im_117_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
