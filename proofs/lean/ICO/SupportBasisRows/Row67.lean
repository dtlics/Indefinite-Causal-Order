import ICO.SupportBasisProducts.Row67
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_67 (b : Fin 25) :
    basisProductRe 67 b.val = (if 67 = 103+b.val then 1 else 0) ∧
    basisProductIm 67 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_67_0, basis_im_67_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_67_1, basis_im_67_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_67_2, basis_im_67_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_67_3, basis_im_67_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_67_4, basis_im_67_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_67_5, basis_im_67_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_67_6, basis_im_67_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_67_7, basis_im_67_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_67_8, basis_im_67_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_67_9, basis_im_67_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_67_10, basis_im_67_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_67_11, basis_im_67_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_67_12, basis_im_67_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_67_13, basis_im_67_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_67_14, basis_im_67_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_67_15, basis_im_67_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_67_16, basis_im_67_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_67_17, basis_im_67_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_67_18, basis_im_67_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_67_19, basis_im_67_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_67_20, basis_im_67_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_67_21, basis_im_67_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_67_22, basis_im_67_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_67_23, basis_im_67_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_67_24, basis_im_67_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
