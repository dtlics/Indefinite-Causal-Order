import ICO.SupportBasisProducts.Row119
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_119 (b : Fin 25) :
    basisProductRe 119 b.val = (if 119 = 103+b.val then 1 else 0) ∧
    basisProductIm 119 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_119_0, basis_im_119_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_119_1, basis_im_119_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_119_2, basis_im_119_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_119_3, basis_im_119_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_119_4, basis_im_119_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_119_5, basis_im_119_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_119_6, basis_im_119_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_119_7, basis_im_119_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_119_8, basis_im_119_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_119_9, basis_im_119_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_119_10, basis_im_119_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_119_11, basis_im_119_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_119_12, basis_im_119_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_119_13, basis_im_119_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_119_14, basis_im_119_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_119_15, basis_im_119_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_119_16, basis_im_119_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_119_17, basis_im_119_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_119_18, basis_im_119_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_119_19, basis_im_119_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_119_20, basis_im_119_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_119_21, basis_im_119_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_119_22, basis_im_119_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_119_23, basis_im_119_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_119_24, basis_im_119_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
