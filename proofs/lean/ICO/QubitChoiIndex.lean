import QIT.Core.Map

namespace ICO.QubitChoiIndex
open Matrix QIT
noncomputable section

def flatten (J : CMatrix (Fin 2 × Fin 4)) : Matrix (Fin 8) (Fin 8) ℂ :=
  fun i j => J ((finProdFinEquiv (m:=2) (n:=4)).symm i)
    ((finProdFinEquiv (m:=2) (n:=4)).symm j)

def unflatten (J : Matrix (Fin 8) (Fin 8) ℂ) : CMatrix (Fin 2 × Fin 4) :=
  fun i j => J (finProdFinEquiv i) (finProdFinEquiv j)

@[simp] theorem flatten_unflatten (J : Matrix (Fin 8) (Fin 8) ℂ) : flatten (unflatten J)=J := by
  ext i j
  simp [flatten,unflatten]

@[simp] theorem unflatten_flatten (J : CMatrix (Fin 2 × Fin 4)) : unflatten (flatten J)=J := by
  ext i j
  simp [flatten,unflatten]

theorem flatten_injective : Function.Injective flatten := by
  intro A B h
  have hh := congrArg unflatten h
  simpa using hh

def flattenLinear : CMatrix (Fin 2 × Fin 4) →ₗ[ℂ] Matrix (Fin 8) (Fin 8) ℂ where
  toFun := flatten
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def unflattenLinear : Matrix (Fin 8) (Fin 8) ℂ →ₗ[ℂ] CMatrix (Fin 2 × Fin 4) where
  toFun := unflatten
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem flatten_add (A B : CMatrix (Fin 2 × Fin 4)) : flatten (A+B)=flatten A+flatten B := rfl
@[simp] theorem flatten_sub (A B : CMatrix (Fin 2 × Fin 4)) : flatten (A-B)=flatten A-flatten B := rfl
@[simp] theorem flatten_smul (r : ℝ) (A : CMatrix (Fin 2 × Fin 4)) : flatten (r • A)=r • flatten A := rfl

#print axioms flatten_injective
end
end ICO.QubitChoiIndex
