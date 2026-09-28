import PoincareConjecture.Definitions.Ch19.CurveEvolution
import PoincareConjecture.Definitions.Ch19.RampEstimates

set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

noncomputable def m62SpatialDerivative (F : RicciFlow n M (Set.Icc a b))
    (c : ℝ → ℝ → M) (t : ℝ)
    (Y : ∀ x, TangentSpace (𝓡 n) (c x t)) (x : ℝ) :
    TangentSpace (𝓡 n) (c x t) :=
  (curveSpeed F c t x)⁻¹ •
    rampHorizontalCovariantDerivative (F.connection t) (fun y ↦ c y t) Y x

noncomputable def m62CurvatureVector (F : RicciFlow n M (Set.Icc a b))
    (c : ℝ → ℝ → M) (t x : ℝ) : TangentSpace (𝓡 n) (c x t) :=
  m62SpatialDerivative F c t (spatialUnitTangent F c t) x

noncomputable def m62CurvatureSquared (F : RicciFlow n M (Set.Icc a b))
    (c : ℝ → ℝ → M) (t x : ℝ) : ℝ :=
  (F.metric t).inner (c x t) (m62CurvatureVector F c t x)
    (m62CurvatureVector F c t x)

noncomputable def m62Curvature (F : RicciFlow n M (Set.Icc a b))
    (c : ℝ → ℝ → M) (t x : ℝ) : ℝ :=
  Real.sqrt (m62CurvatureSquared F c t x)

noncomputable def m62SpatialNormalDerivative (F : RicciFlow n M (Set.Icc a b))
    (c : ℝ → ℝ → M) (t x : ℝ) : TangentSpace (𝓡 n) (c x t) :=
  let A := m62SpatialDerivative F c t (m62CurvatureVector F c t) x
  let S := spatialUnitTangent F c t x
  A - (F.metric t).inner (c x t) A S • S

noncomputable def m62ArcDerivative (F : RicciFlow n M (Set.Icc a b))
    (c : ℝ → ℝ → M) (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (curveSpeed F c t x)⁻¹ * deriv f x

noncomputable def m62ArcSecondDerivative (F : RicciFlow n M (Set.Icc a b))
    (c : ℝ → ℝ → M) (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  m62ArcDerivative F c t (m62ArcDerivative F c t f) x

noncomputable def m62RegularizedCurvature (F : RicciFlow n M (Set.Icc a b))
    (c : ℝ → ℝ → M) (ε t x : ℝ) : ℝ :=
  Real.sqrt (m62CurvatureSquared F c t x + ε ^ 2)

noncomputable def m62Length (F : RicciFlow n M (Set.Icc a b))
    (c : ℝ → ℝ → M) (t : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..curvePeriod, curveSpeed F c t x

noncomputable def m62TotalCurvature (F : RicciFlow n M (Set.Icc a b))
    (c : ℝ → ℝ → M) (t : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..curvePeriod, m62Curvature F c t x * curveSpeed F c t x

noncomputable def m62RegularizedTotalCurvature (F : RicciFlow n M (Set.Icc a b))
    (c : ℝ → ℝ → M) (ε t : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..curvePeriod,
    m62RegularizedCurvature F c ε t x * curveSpeed F c t x

noncomputable def m62TangentRicci (F : RicciFlow n M (Set.Icc a b))
    (c : ℝ → ℝ → M) (t x : ℝ) : ℝ :=
  (F.connection t).ricci (c x t) (spatialUnitTangent F c t x)
    (spatialUnitTangent F c t x)

structure M62ShrinkingCurve (F : RicciFlow n M (Set.Icc a b))
    (c : ℝ → ℝ → M) : Prop where
  periodic : ∀ t ∈ Set.Icc a b, ∀ x, c (x + curvePeriod) t = c x t
  spatial_regular : ∀ t ∈ Set.Icc a b,
    ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) 2 (fun x ↦ c x t)
  joint_smooth : ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) (𝓡 n) ∞
    (fun z : ℝ × ℝ ↦ c z.1 z.2) (Set.univ ×ˢ Set.Ioo a b)
  immersed : ∀ t ∈ Set.Icc a b, ∀ x,
    curveVelocity (n := n) (fun y ↦ c y t) x ≠ 0
  continuous : ContinuousOn (fun z : ℝ × ℝ ↦ c z.1 z.2)
    (Set.univ ×ˢ Set.Icc a b)
  velocity_continuous : ContinuousOn
    (fun z : ℝ × ℝ ↦ (⟨c z.1 z.2,
      curveVelocity (n := n) (fun y ↦ c y z.2) z.1⟩ : TangentBundle (𝓡 n) M))
    (Set.univ ×ˢ Set.Icc a b)
  curvature_continuous : ContinuousOn
    (fun z : ℝ × ℝ ↦ (⟨c z.1 z.2, m62CurvatureVector F c z.2 z.1⟩ :
      TangentBundle (𝓡 n) M)) (Set.univ ×ˢ Set.Icc a b)
  equation : ∀ t ∈ Set.Ioo a b, ∀ x,
    curveVelocity (n := n) (fun s ↦ c x s) t = m62CurvatureVector F c t x

def m62C0 (K0 K1 K2 : ℝ) : ℝ :=
  2 * K0 + 6 * K2 + 2 * K2 ^ 2 + 6 * K1

noncomputable def m62C1 (K0 K1 K2 : ℝ) : ℝ := m62C0 K0 K1 K2 / 2

end PoincareConjecture
