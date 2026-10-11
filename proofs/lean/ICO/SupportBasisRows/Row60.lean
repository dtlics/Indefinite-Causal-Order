import ICO.SupportBasisProducts.Row60
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_60 (b : Fin 25) :
    basisProductRe 60 b.val = (if 60 = 103+b.val then 1 else 0) ∧
    basisProductIm 60 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_60_0, basis_im_60_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_60_1, basis_im_60_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_60_2, basis_im_60_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_60_3, basis_im_60_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_60_4, basis_im_60_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_60_5, basis_im_60_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_60_6, basis_im_60_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_60_7, basis_im_60_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_60_8, basis_im_60_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_60_9, basis_im_60_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_60_10, basis_im_60_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_60_11, basis_im_60_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_60_12, basis_im_60_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_60_13, basis_im_60_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_60_14, basis_im_60_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_60_15, basis_im_60_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_60_16, basis_im_60_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_60_17, basis_im_60_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_60_18, basis_im_60_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_60_19, basis_im_60_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_60_20, basis_im_60_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_60_21, basis_im_60_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_60_22, basis_im_60_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_60_23, basis_im_60_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_60_24, basis_im_60_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
