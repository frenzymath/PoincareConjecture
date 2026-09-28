import PoincareConjecture.Definitions.Ch06.LGeometry

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem tangent_totalSpace_cast {x y : M} (h : x = y) (v : TangentSpace (𝓡 n) x) :
    Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y (h ▸ v) =
      Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) x v := by
  cases h
  rfl

theorem tangent_eq_of_totalSpace_eq {x y : M} (h : x = y)
    {v : TangentSpace (𝓡 n) x} {w : TangentSpace (𝓡 n) y}
    (heq : Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) x v =
      Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y w) : v = h.symm ▸ w := by
  cases h
  exact Bundle.TotalSpace.mk_injective x heq

theorem tangent_cast_zero {x y : M} (h : x = y) :
    (h ▸ (0 : TangentSpace (𝓡 n) x)) = (0 : TangentSpace (𝓡 n) y) := by
  cases h
  rfl

variable {J : Set ℝ} {F : RicciFlow n M J} {T τ₁ τ₂ : ℝ}
  {p : BackwardTimePath F T τ₁ τ₂}

theorem sqrt_mem_sqrtParameterInterval {τ : ℝ} (hτ : τ ∈ Icc τ₁ τ₂) :
    Real.sqrt τ ∈ sqrtParameterInterval τ₁ τ₂ :=
  ⟨Real.sqrt_le_sqrt hτ.1, Real.sqrt_le_sqrt hτ.2⟩

theorem square_mem_backward_interval (p : BackwardTimePath F T τ₁ τ₂)
    {s : ℝ} (hs : s ∈ sqrtParameterInterval τ₁ τ₂) : s ^ 2 ∈ Icc τ₁ τ₂ := by
  have hsn : 0 ≤ s := (Real.sqrt_nonneg τ₁).trans hs.1
  constructor
  · simpa only [Real.sq_sqrt p.nonnegative] using
      (sq_le_sq₀ (Real.sqrt_nonneg τ₁) hsn).mpr hs.1
  · simpa only [Real.sq_sqrt (p.nonnegative.trans p.ordered.le)] using
      (sq_le_sq₀ hsn (Real.sqrt_nonneg τ₂)).mpr hs.2

theorem sqrtRegularPath_point_eq (R : SqrtRegularPath p) {τ : ℝ}
    (hτ : τ ∈ Icc τ₁ τ₂) : R.curve (Real.sqrt τ) = p.curve τ :=
  (R.agrees _ (sqrt_mem_sqrtParameterInterval hτ)).trans
    (congrArg p.curve (Real.sq_sqrt (p.nonnegative.trans hτ.1)))

def backwardFieldOfSqrt (R : SqrtRegularPath p)
    (Yhat : ∀ s, TangentSpace (𝓡 n) (R.curve s)) (τ : ℝ) :
    TangentSpace (𝓡 n) (p.curve τ) := by
  classical
  exact if hτ : τ ∈ Icc τ₁ τ₂ then sqrtRegularPath_point_eq R hτ ▸ Yhat (Real.sqrt τ)
    else 0

theorem backwardFieldOfSqrt_totalSpace (R : SqrtRegularPath p)
    (Yhat : ∀ s, TangentSpace (𝓡 n) (R.curve s)) {τ : ℝ}
    (hτ : τ ∈ Icc τ₁ τ₂) :
    Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (p.curve τ) (backwardFieldOfSqrt R Yhat τ) =
      Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (R.curve (Real.sqrt τ))
        (Yhat (Real.sqrt τ)) := by
  rw [backwardFieldOfSqrt, dif_pos hτ]
  exact tangent_totalSpace_cast (sqrtRegularPath_point_eq R hτ) _

theorem backwardFieldOfSqrt_agrees (R : SqrtRegularPath p)
    (Yhat : ∀ s, TangentSpace (𝓡 n) (R.curve s)) {s : ℝ}
    (hs : s ∈ sqrtParameterInterval τ₁ τ₂) :
    Yhat s = (R.agrees s hs).symm ▸ backwardFieldOfSqrt R Yhat (s ^ 2) := by
  have h := backwardFieldOfSqrt_totalSpace R Yhat (square_mem_backward_interval p hs)
  rw [Real.sqrt_sq ((Real.sqrt_nonneg τ₁).trans hs.1)] at h
  exact tangent_eq_of_totalSpace_eq (R.agrees s hs) h.symm

theorem backwardFieldOfSqrt_initial_zero (R : SqrtRegularPath p)
    (Yhat : ∀ s, TangentSpace (𝓡 n) (R.curve s))
    (hY : Yhat (Real.sqrt τ₁) = 0) : backwardFieldOfSqrt R Yhat τ₁ = 0 := by
  have hτ : τ₁ ∈ Icc τ₁ τ₂ := ⟨le_rfl, p.ordered.le⟩
  rw [backwardFieldOfSqrt, dif_pos hτ, hY]
  exact tangent_cast_zero (sqrtRegularPath_point_eq R hτ)

def sqrtRegularFieldOfPullback (R : SqrtRegularPath p)
    (Yhat P : ∀ s, TangentSpace (𝓡 n) (R.curve s))
    (E : ParametricAlongCurveExtensionOn (sqrtParameterInterval τ₁ τ₂) R.curve Yhat)
    (EP : ParametricAlongCurveExtensionOn (sqrtParameterInterval τ₁ τ₂) R.curve P)
    (hP : ∀ s ∈ sqrtParameterInterval τ₁ τ₂,
      pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) R.curve Yhat
        (sqrtParameterInterval τ₁ τ₂) E s = P s) :
    SqrtRegularField R (backwardFieldOfSqrt R Yhat) where
  field := Yhat
  agrees s hs := backwardFieldOfSqrt_agrees R Yhat hs
  extension := E
  derivative_extension := {
    extension := EP.extension
    domain := EP.domain
    open_domain := EP.open_domain
    graph_mem := EP.graph_mem
    smooth := EP.smooth
    agrees := fun s hs ↦ (EP.agrees s hs).trans (hP s hs).symm }

theorem sqrtRegularFieldOfPullback_firstDerivative (R : SqrtRegularPath p)
    (Yhat P : ∀ s, TangentSpace (𝓡 n) (R.curve s))
    (E : ParametricAlongCurveExtensionOn (sqrtParameterInterval τ₁ τ₂) R.curve Yhat)
    (EP : ParametricAlongCurveExtensionOn (sqrtParameterInterval τ₁ τ₂) R.curve P)
    (hP : ∀ s ∈ sqrtParameterInterval τ₁ τ₂,
      pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) R.curve Yhat
        (sqrtParameterInterval τ₁ τ₂) E s = P s)
    {s : ℝ} (hs : s ∈ sqrtParameterInterval τ₁ τ₂) :
    (sqrtRegularFieldOfPullback R Yhat P E EP hP).firstDerivative s = P s := hP s hs

theorem sqrtRegularField_totalSpace_agrees {R : SqrtRegularPath p}
    {Y : ∀ τ, TangentSpace (𝓡 n) (p.curve τ)} (Q : SqrtRegularField R Y)
    {s : ℝ} (hs : s ∈ sqrtParameterInterval τ₁ τ₂) :
    Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (R.curve s) (Q.field s) =
      Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (p.curve (s ^ 2)) (Y (s ^ 2)) := by
  rw [Q.agrees s hs]
  exact tangent_totalSpace_cast (R.agrees s hs).symm _

theorem sqrtRegularField_eq_of_totalSpace_eq {R R' : SqrtRegularPath p}
    {Y Z : ∀ τ, TangentSpace (𝓡 n) (p.curve τ)}
    (Q : SqrtRegularField R Y) (Q' : SqrtRegularField R' Z)
    (heq : ∀ s ∈ sqrtParameterInterval τ₁ τ₂,
      Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (R.curve s) (Q.field s) =
        Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (R'.curve s) (Q'.field s)) :
    ∀ τ ∈ Icc τ₁ τ₂, Y τ = Z τ := by
  intro τ hτ
  have hs := sqrt_mem_sqrtParameterInterval hτ
  have h := (sqrtRegularField_totalSpace_agrees Q hs).symm.trans
    ((heq (Real.sqrt τ) hs).trans (sqrtRegularField_totalSpace_agrees Q' hs))
  have hf := Bundle.TotalSpace.mk_injective (p.curve ((Real.sqrt τ) ^ 2)) h
  exact (congrArg (fun r : ℝ ↦ Y r = Z r)
    (Real.sq_sqrt (p.nonnegative.trans hτ.1))).mp hf

end PoincareConjecture.M08
