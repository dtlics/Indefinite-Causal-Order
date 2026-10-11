import ICO.SupportBasisProducts.Row52
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_52 (b : Fin 25) :
    basisProductRe 52 b.val = (if 52 = 103+b.val then 1 else 0) ∧
    basisProductIm 52 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_52_0, basis_im_52_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_52_1, basis_im_52_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_52_2, basis_im_52_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_52_3, basis_im_52_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_52_4, basis_im_52_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_52_5, basis_im_52_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_52_6, basis_im_52_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_52_7, basis_im_52_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_52_8, basis_im_52_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_52_9, basis_im_52_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_52_10, basis_im_52_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_52_11, basis_im_52_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_52_12, basis_im_52_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_52_13, basis_im_52_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_52_14, basis_im_52_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_52_15, basis_im_52_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_52_16, basis_im_52_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_52_17, basis_im_52_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_52_18, basis_im_52_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_52_19, basis_im_52_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_52_20, basis_im_52_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_52_21, basis_im_52_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_52_22, basis_im_52_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_52_23, basis_im_52_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_52_24, basis_im_52_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
