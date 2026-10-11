import ICO.SupportBasisProducts.Row78
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_78 (b : Fin 25) :
    basisProductRe 78 b.val = (if 78 = 103+b.val then 1 else 0) ∧
    basisProductIm 78 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_78_0, basis_im_78_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_78_1, basis_im_78_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_78_2, basis_im_78_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_78_3, basis_im_78_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_78_4, basis_im_78_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_78_5, basis_im_78_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_78_6, basis_im_78_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_78_7, basis_im_78_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_78_8, basis_im_78_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_78_9, basis_im_78_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_78_10, basis_im_78_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_78_11, basis_im_78_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_78_12, basis_im_78_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_78_13, basis_im_78_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_78_14, basis_im_78_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_78_15, basis_im_78_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_78_16, basis_im_78_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_78_17, basis_im_78_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_78_18, basis_im_78_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_78_19, basis_im_78_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_78_20, basis_im_78_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_78_21, basis_im_78_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_78_22, basis_im_78_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_78_23, basis_im_78_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_78_24, basis_im_78_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
