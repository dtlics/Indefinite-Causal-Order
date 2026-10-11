import ICO.TensorRowOperators
import ICO.QubitTensorGauge

namespace ICO.TensorBitOrder
open ICO.ExactTensorCertificates
open Matrix
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def modIndex (i : Nat) : Fin 128 := ⟨i%128, Nat.mod_lt _ (by decide)⟩

def periodicTensor {R : Type*} (C : Matrix (Fin 128) (Fin 128) R) : Nat → Nat → R :=
  fun i j => C (modIndex i) (modIndex j)

theorem modIndex_fin (i : Fin 128) : modIndex i.val = i := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt i.isLt

theorem basisEntry_mod128 (i k : Nat) : basisEntry (i%128) k = basisEntry i k := by
  have h0 : (i%128)/64%2 = i/64%2 := by omega
  have h1 : (i%128)/32%2 = i/32%2 := by omega
  have h2 : (i%128)/16%2 = i/16%2 := by omega
  have h3 : (i%128)/8%2 = i/8%2 := by omega
  have h4 : (i%128)/4%2 = i/4%2 := by omega
  have h5 : (i%128)/2%2 = i/2%2 := by omega
  have h6 : i%128%2 = i%2 := by omega
  simp only [basisEntry, h0, h1, h2, h3, h4, h5, h6]

theorem choiCoefficient_mod128 (a b i j : Nat) :
    choiCoefficient a b (i%128) (j%128) = choiCoefficient a b i j := by
  simp only [choiCoefficient, basisEntry_mod128]

def pack (o : Fin 8) (a b : Fin 4) : Fin 128 :=
  ⟨(o.val/4)*64+a.val*16+b.val*4+o.val%4, by omega⟩

def external (i : Fin 128) : Fin 8 := ⟨(i.val/64)*4+i.val%4, by omega⟩
def slotA (i : Fin 128) : Fin 4 := ⟨i.val/16%4, Nat.mod_lt _ (by decide)⟩
def slotB (i : Fin 128) : Fin 4 := ⟨i.val/4%4, Nat.mod_lt _ (by decide)⟩

theorem pack_unpack (i : Fin 128) : pack (external i) (slotA i) (slotB i) = i := by
  apply Fin.ext
  dsimp [pack, external, slotA, slotB]
  omega

theorem unpack_pack (o : Fin 8) (a b : Fin 4) :
    external (pack o a b) = o ∧ slotA (pack o a b) = a ∧ slotB (pack o a b) = b := by
  constructor
  · apply Fin.ext; dsimp [pack, external]; omega
  constructor
  · apply Fin.ext; dsimp [pack, slotA]; omega
  · apply Fin.ext; dsimp [pack, slotB]; omega

def slotTensor {R : Type*} (C : Matrix (Fin 128) (Fin 128) R) (o p : Fin 8) :
    Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) R :=
  fun a b => C (pack o a.1 b.1) (pack p a.2 b.2)

def slotTensorNat {R : Type*} (C : Nat → Nat → R) (o p : Fin 8) :
    Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) R :=
  fun a b => C (pack o a.1 b.1).val (pack p a.2 b.2).val

theorem pack_AO (o : Fin 8) (a b : Fin 4) : (pack o a b).val/16%2 = a.val%2 := by
  dsimp [pack]; omega
theorem pack_A (o : Fin 8) (a b : Fin 4) : (pack o a b).val/16%4 = a.val := by
  dsimp [pack]; omega
theorem pack_BO (o : Fin 8) (a b : Fin 4) : (pack o a b).val/4%2 = b.val%2 := by
  dsimp [pack]; omega
theorem pack_B (o : Fin 8) (a b : Fin 4) : (pack o a b).val/4%4 = b.val := by
  dsimp [pack]; omega

theorem replace_AO (o : Fin 8) (a b : Fin 4) (h : Fin 2) :
    (pack o a b).val/32*32+h.val*16+(pack o a b).val%16 =
      (pack o ⟨2*(a.val/2)+h.val, by omega⟩ b).val := by
  dsimp [pack]; omega
theorem replace_A (o : Fin 8) (a b h : Fin 4) :
    (pack o a b).val/64*64+h.val*16+(pack o a b).val%16 = (pack o h b).val := by
  dsimp [pack]; omega
theorem replace_BO (o : Fin 8) (a b : Fin 4) (h : Fin 2) :
    (pack o a b).val/8*8+h.val*4+(pack o a b).val%4 =
      (pack o a ⟨2*(b.val/2)+h.val, by omega⟩).val := by
  dsimp [pack]; omega
theorem replace_B (o : Fin 8) (a b h : Fin 4) :
    (pack o a b).val/16*16+h.val*4+(pack o a b).val%4 = (pack o a h).val := by
  dsimp [pack]; omega

theorem projectA4_pack (C : Nat → Nat → ℂ) (o p : Fin 8) (a a' b b' : Fin 4) :
    TensorRowOperators.projectA4 C (pack o a b).val (pack p a' b').val =
      QubitCPTPGauge.lambdaFour
        (fun s t => C (pack o s b).val (pack p t b').val) a a' := by
  simp only [TensorRowOperators.projectA4, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, TensorRowOperators.traceReplace,
    LinearMap.coe_mk, AddHom.coe_mk, pack_AO, pack_A,
    QubitCPTPGauge.lambdaFour, Matrix.trace, Matrix.diag_apply]
  simp only [show 16*2 = 32 from rfl, show 16*4 = 64 from rfl,
    replace_AO, replace_A, beq_iff_eq, Fin.val_inj]

theorem projectB4_pack (C : Nat → Nat → ℂ) (o p : Fin 8) (a a' b b' : Fin 4) :
    TensorRowOperators.projectB4 C (pack o a b).val (pack p a' b').val =
      QubitCPTPGauge.lambdaFour
        (fun s t => C (pack o a s).val (pack p a' t).val) b b' := by
  simp only [TensorRowOperators.projectB4, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, TensorRowOperators.traceReplace,
    LinearMap.coe_mk, AddHom.coe_mk, pack_BO, pack_B,
    QubitCPTPGauge.lambdaFour, Matrix.trace, Matrix.diag_apply]
  simp only [show 4*2 = 8 from rfl, show 4*4 = 16 from rfl,
    replace_BO, replace_B, beq_iff_eq, Fin.val_inj]

theorem projectA4_slotTensor (C : Nat → Nat → ℂ) (o p : Fin 8) :
    slotTensorNat (TensorRowOperators.projectA4 C) o p =
      QubitTensorGauge.lambdaMatrix * slotTensorNat C o p := by
  ext a b
  rw [slotTensorNat, projectA4_pack, QubitCPTPGauge.lambdaFour_coefficients]
  simp [Matrix.mul_apply, Fintype.sum_prod_type, QubitTensorGauge.lambdaMatrix, slotTensorNat]

theorem projectB4_slotTensor (C : Nat → Nat → ℂ) (o p : Fin 8) :
    slotTensorNat (TensorRowOperators.projectB4 C) o p =
      slotTensorNat C o p * QubitTensorGauge.lambdaMatrixᵀ := by
  ext a b
  rw [slotTensorNat, projectB4_pack, QubitCPTPGauge.lambdaFour_coefficients]
  simp [Matrix.mul_apply, Fintype.sum_prod_type, QubitTensorGauge.lambdaMatrix,
    slotTensorNat, Matrix.transpose_apply, mul_comm]

theorem gauge_slotTensor (C : Nat → Nat → ℂ) (o p : Fin 8) :
    slotTensorNat (TensorRowOperators.projectA4 (TensorRowOperators.projectB4 C)) o p =
      QubitTensorGauge.lambdaMatrix * slotTensorNat C o p * QubitTensorGauge.lambdaMatrixᵀ := by
  rw [projectA4_slotTensor, projectB4_slotTensor, Matrix.mul_assoc]

theorem gaugeRow_zero_of_channels (C : Nat → Nat → ℂ)
    (h : ∀ (o p : Fin 8) (A B : QubitCPTPGauge.SlotMatrix),
      QubitCPTPGauge.IsChannelChoi A → QubitCPTPGauge.IsChannelChoi B →
      QubitTensorGauge.contract (slotTensorNat C o p) A B = 0)
    (k : Nat) (hk : k < 16384) : TensorRowOperators.gaugeRow k C = 0 := by
  let i : Fin 128 := ⟨k%128, Nat.mod_lt _ (by decide)⟩
  let j : Fin 128 := ⟨k/128, by omega⟩
  have hz := QubitTensorGauge.gauge_zero_of_channel_tests
    (slotTensorNat C (external i) (external j)) (h (external i) (external j))
  rw [← gauge_slotTensor] at hz
  have he := congrFun (congrFun hz (slotA i, slotA j)) (slotB i, slotB j)
  simpa [slotTensorNat, pack_unpack, TensorRowOperators.gaugeRow,
    TensorRowOperators.evalAt, i, j] using he

end ICO.TensorBitOrder
