import ICO.SupportBasisProducts.Row100
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_100 (b : Fin 25) :
    basisProductRe 100 b.val = (if 100 = 103+b.val then 1 else 0) ∧
    basisProductIm 100 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_100_0, basis_im_100_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_100_1, basis_im_100_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_100_2, basis_im_100_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_100_3, basis_im_100_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_100_4, basis_im_100_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_100_5, basis_im_100_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_100_6, basis_im_100_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_100_7, basis_im_100_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_100_8, basis_im_100_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_100_9, basis_im_100_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_100_10, basis_im_100_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_100_11, basis_im_100_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_100_12, basis_im_100_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_100_13, basis_im_100_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_100_14, basis_im_100_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_100_15, basis_im_100_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_100_16, basis_im_100_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_100_17, basis_im_100_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_100_18, basis_im_100_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_100_19, basis_im_100_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_100_20, basis_im_100_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_100_21, basis_im_100_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_100_22, basis_im_100_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_100_23, basis_im_100_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_100_24, basis_im_100_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
