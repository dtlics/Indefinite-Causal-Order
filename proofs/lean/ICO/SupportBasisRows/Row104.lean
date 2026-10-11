import ICO.SupportBasisProducts.Row104
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem basis_row_104 (b : Fin 25) :
    basisProductRe 104 b.val = (if 104 = 103+b.val then 1 else 0) ∧
    basisProductIm 104 b.val = 0 := by
  match b with
  | ⟨0, _⟩ => exact ⟨basis_re_104_0, basis_im_104_0⟩
  | ⟨1, _⟩ => exact ⟨basis_re_104_1, basis_im_104_1⟩
  | ⟨2, _⟩ => exact ⟨basis_re_104_2, basis_im_104_2⟩
  | ⟨3, _⟩ => exact ⟨basis_re_104_3, basis_im_104_3⟩
  | ⟨4, _⟩ => exact ⟨basis_re_104_4, basis_im_104_4⟩
  | ⟨5, _⟩ => exact ⟨basis_re_104_5, basis_im_104_5⟩
  | ⟨6, _⟩ => exact ⟨basis_re_104_6, basis_im_104_6⟩
  | ⟨7, _⟩ => exact ⟨basis_re_104_7, basis_im_104_7⟩
  | ⟨8, _⟩ => exact ⟨basis_re_104_8, basis_im_104_8⟩
  | ⟨9, _⟩ => exact ⟨basis_re_104_9, basis_im_104_9⟩
  | ⟨10, _⟩ => exact ⟨basis_re_104_10, basis_im_104_10⟩
  | ⟨11, _⟩ => exact ⟨basis_re_104_11, basis_im_104_11⟩
  | ⟨12, _⟩ => exact ⟨basis_re_104_12, basis_im_104_12⟩
  | ⟨13, _⟩ => exact ⟨basis_re_104_13, basis_im_104_13⟩
  | ⟨14, _⟩ => exact ⟨basis_re_104_14, basis_im_104_14⟩
  | ⟨15, _⟩ => exact ⟨basis_re_104_15, basis_im_104_15⟩
  | ⟨16, _⟩ => exact ⟨basis_re_104_16, basis_im_104_16⟩
  | ⟨17, _⟩ => exact ⟨basis_re_104_17, basis_im_104_17⟩
  | ⟨18, _⟩ => exact ⟨basis_re_104_18, basis_im_104_18⟩
  | ⟨19, _⟩ => exact ⟨basis_re_104_19, basis_im_104_19⟩
  | ⟨20, _⟩ => exact ⟨basis_re_104_20, basis_im_104_20⟩
  | ⟨21, _⟩ => exact ⟨basis_re_104_21, basis_im_104_21⟩
  | ⟨22, _⟩ => exact ⟨basis_re_104_22, basis_im_104_22⟩
  | ⟨23, _⟩ => exact ⟨basis_re_104_23, basis_im_104_23⟩
  | ⟨24, _⟩ => exact ⟨basis_re_104_24, basis_im_104_24⟩
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
