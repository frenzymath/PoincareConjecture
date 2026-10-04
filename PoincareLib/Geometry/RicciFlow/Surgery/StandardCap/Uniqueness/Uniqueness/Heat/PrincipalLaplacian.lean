import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Uniqueness.Heat.PrincipalResponse

/-!
# Identifying the actual variable-coefficient Dirichlet generator

Morgan-Tian, Section 12.5, p. 304: integration by parts identifies the
constructed compact-domain form with the divergence of its literal
coefficient flux. The coefficient derivative is retained; it contributes
to the first-order correction for the actual raw vector heat equation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped Topology SchwartzMap LineDeriv

namespace PoincareMT.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckGeneratorRegularityNative

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

/-- Actual coefficient multiplication preserves the supported test space. -/
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

/-- The literal divergence of the actual coefficient flux. -/
def principalTestLaplacian {K : Set V} (hK : IsClosed K)
    (A : Fin n → Fin n → 𝓢(V, ℝ)) : supportedTests K →ₗ[ℝ] supportedTests K :=
  ∑ i, ∑ j, (testPartial hK i).comp ((testMultiplier K (A i j)).comp (testPartial hK j))

/-- Section 12.5, p. 304: the actual coefficient energy has exactly
the integration-by-parts pairing required by the constructed generator. -/
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

/-- The actual variational generator equals minus the literal
variable-coefficient divergence Laplacian on supported smooth tests. -/
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

end PoincareMT.M35.Uniqueness.Heat
