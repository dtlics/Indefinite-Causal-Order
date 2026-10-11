import ICO.SupportBasisProducts.Row50
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_50 (b : Fin 25) :
    basisProductRe 50 b.val = (if 50 = 103+b.val then 1 else 0) ∧
    basisProductIm 50 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_50_0, basis_im_50_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_50_1, basis_im_50_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_50_2, basis_im_50_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_50_3, basis_im_50_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_50_4, basis_im_50_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_50_5, basis_im_50_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_50_6, basis_im_50_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_50_7, basis_im_50_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_50_8, basis_im_50_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_50_9, basis_im_50_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_50_10, basis_im_50_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_50_11, basis_im_50_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_50_12, basis_im_50_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_50_13, basis_im_50_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_50_14, basis_im_50_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_50_15, basis_im_50_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_50_16, basis_im_50_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_50_17, basis_im_50_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_50_18, basis_im_50_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_50_19, basis_im_50_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_50_20, basis_im_50_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_50_21, basis_im_50_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_50_22, basis_im_50_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_50_23, basis_im_50_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_50_24, basis_im_50_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
