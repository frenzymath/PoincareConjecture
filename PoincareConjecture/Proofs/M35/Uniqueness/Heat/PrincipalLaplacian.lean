import PoincareConjecture.Proofs.M35.Uniqueness.Heat.PrincipalResponse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped Topology SchwartzMap LineDeriv

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckGeneratorRegularityNative

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

def testMultiplier (K : Set V) (a : 𝓢(V, ℝ)) :
    supportedTests K →ₗ[ℝ] supportedTests K :=
  (((SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) a).toLinearMap.comp
    (supportedTests K).subtype)).codRestrict (supportedTests K) (fun f => by
      intro x hx
      change a x * (f : 𝓢(V, ℝ)) x = 0
      rw [f.property x hx, mul_zero])

theorem testMultiplier_toLp (K : Set V) (a : 𝓢(V, ℝ)) (f : supportedTests K) :
    (testMultiplier K a f : 𝓢(V, ℝ)).toLp 2 volume =
      schwartzMultiplier a ((f : 𝓢(V, ℝ)).toLp 2 volume) := by
  apply Lp.ext
  filter_upwards [(testMultiplier K a f : 𝓢(V, ℝ)).coeFn_toLp 2 volume,
    schwartzMultiplier_coe a ((f : 𝓢(V, ℝ)).toLp 2 volume),
    (f : 𝓢(V, ℝ)).coeFn_toLp 2 volume] with x hp hm hf
  rw [hp, hm, hf]
  rfl

def principalTestLaplacian {K : Set V} (hK : IsClosed K)
    (A : Fin n → Fin n → 𝓢(V, ℝ)) : supportedTests K →ₗ[ℝ] supportedTests K :=
  ∑ i, ∑ j, (testPartial hK i).comp ((testMultiplier K (A i j)).comp (testPartial hK j))

theorem principalEnergy_pairing_laplacian {K : Set V} (hK : IsClosed K)
    (A : Fin n → Fin n → 𝓢(V, ℝ)) (φ f : supportedTests K) :
    principalEnergy K A (intoDirichletForm K φ) (intoDirichletForm K f) =
      -inner ℝ (intoDirichletValue K φ)
        (intoDirichletValue K (principalTestLaplacian hK A f)) := by
  simp only [principalEnergy, dirichletPartial_into, principalTestLaplacian,
    LinearMap.sum_apply, map_sum, inner_sum]
  simp_rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [schwartzMultiplier_selfAdjoint]
  have hm := testMultiplier_toLp K (A i j) (testPartial hK j f)
  change (testMultiplier K (A i j) (testPartial hK j f) : 𝓢(V, ℝ)).toLp 2 volume =
    schwartzMultiplier (A i j)
      ((∂_{EuclideanSpace.single j (1 : ℝ)} (f : 𝓢(V, ℝ))).toLp 2 volume) at hm
  rw [← hm]
  have hp := inner_schwartzLineDeriv (φ : 𝓢(V, ℝ))
    (testMultiplier K (A i j) (testPartial hK j f) : 𝓢(V, ℝ))
    (EuclideanSpace.single i (1 : ℝ))
  change inner ℝ
      ((∂_{EuclideanSpace.single i (1 : ℝ)} (φ : 𝓢(V, ℝ))).toLp 2 volume)
      ((testMultiplier K (A i j) (testPartial hK j f) : 𝓢(V, ℝ)).toLp 2 volume) =
    -inner ℝ ((φ : 𝓢(V, ℝ)).toLp 2 volume)
      ((∂_{EuclideanSpace.single i (1 : ℝ)}
        (testMultiplier K (A i j) (testPartial hK j f) : 𝓢(V, ℝ))).toLp 2 volume)
  linarith only [hp]

theorem principalForm_pairing_laplacian {K : Set V} (hK : IsClosed K)
    (A : Fin n → Fin n → 𝓢(V, ℝ)) (f : supportedTests K) (u : dirichletForm K) :
    principalFormPairing K A u (intoDirichletForm K f) =
      inner ℝ (dirichletInclusion K u)
        (intoDirichletValue K f - intoDirichletValue K (principalTestLaplacian hK A f)) := by
  have he : (fun u : dirichletForm K => principalFormPairing K A u (intoDirichletForm K f)) =
      (fun u => inner ℝ (dirichletInclusion K u)
        (intoDirichletValue K f - intoDirichletValue K (principalTestLaplacian hK A f))) := by
    apply (intoDirichletForm_denseRange K).equalizer
      ((principalFormPairing_continuous K A).comp (continuous_id.prodMk continuous_const))
      ((dirichletInclusion K).continuous.inner continuous_const)
    funext φ
    simp only [Function.comp_apply, id_eq, principalFormPairing, dirichletInclusion_into,
      principalEnergy_pairing_laplacian hK, inner_sub_right]
    ring
  exact congrFun he u

end PoincareConjecture.M35.Uniqueness.Heat
