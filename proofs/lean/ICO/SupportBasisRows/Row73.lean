import ICO.SupportBasisProducts.Row73
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_73 (b : Fin 25) :
    basisProductRe 73 b.val = (if 73 = 103+b.val then 1 else 0) ∧
    basisProductIm 73 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_73_0, basis_im_73_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_73_1, basis_im_73_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_73_2, basis_im_73_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_73_3, basis_im_73_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_73_4, basis_im_73_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_73_5, basis_im_73_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_73_6, basis_im_73_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_73_7, basis_im_73_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_73_8, basis_im_73_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_73_9, basis_im_73_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_73_10, basis_im_73_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_73_11, basis_im_73_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_73_12, basis_im_73_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_73_13, basis_im_73_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_73_14, basis_im_73_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_73_15, basis_im_73_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_73_16, basis_im_73_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_73_17, basis_im_73_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_73_18, basis_im_73_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_73_19, basis_im_73_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_73_20, basis_im_73_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_73_21, basis_im_73_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_73_22, basis_im_73_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_73_23, basis_im_73_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_73_24, basis_im_73_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
