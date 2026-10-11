import ICO.SupportBasisProducts.Row69
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_69 (b : Fin 25) :
    basisProductRe 69 b.val = (if 69 = 103+b.val then 1 else 0) ∧
    basisProductIm 69 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_69_0, basis_im_69_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_69_1, basis_im_69_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_69_2, basis_im_69_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_69_3, basis_im_69_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_69_4, basis_im_69_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_69_5, basis_im_69_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_69_6, basis_im_69_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_69_7, basis_im_69_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_69_8, basis_im_69_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_69_9, basis_im_69_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_69_10, basis_im_69_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_69_11, basis_im_69_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_69_12, basis_im_69_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_69_13, basis_im_69_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_69_14, basis_im_69_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_69_15, basis_im_69_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_69_16, basis_im_69_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_69_17, basis_im_69_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_69_18, basis_im_69_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_69_19, basis_im_69_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_69_20, basis_im_69_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_69_21, basis_im_69_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_69_22, basis_im_69_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_69_23, basis_im_69_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_69_24, basis_im_69_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
