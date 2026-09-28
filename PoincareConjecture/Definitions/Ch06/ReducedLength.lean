import PoincareConjecture.Definitions.Ch06.LGeometry
import PoincareConjecture.Definitions.Ch01.ScalarOperators
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Defs

set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral BigOperators

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

noncomputable def reducedHarnackDensity {J : Set ℝ}
    (F : RicciFlow n M J) (T : ℝ) (γ : ℝ → M)
    (timeDerivative : ℝ → ℝ) (τ : ℝ) : ℝ :=
  -timeDerivative τ -
    (F.connection (T - τ)).scalarCurvature (γ τ) / τ -
    2 * (mvfderiv (𝓡 n)
      (fun y ↦ (F.connection (T - τ)).scalarCurvature y) (γ τ))
      (curveVelocity (n := n) γ τ) +
    2 * (F.connection (T - τ)).ricci (γ τ)
      (curveVelocity (n := n) γ τ) (curveVelocity (n := n) γ τ)

noncomputable def reducedHarnackIntegral {J : Set ℝ}
    (F : RicciFlow n M J) (T : ℝ) (γ : ℝ → M)
    (timeDerivative : ℝ → ℝ) (τ : ℝ) : ℝ :=
  ∫ s in 0..τ, s * Real.sqrt s * reducedHarnackDensity F T γ timeDerivative s

noncomputable def reducedLengthGradientNormSq {J : Set ℝ}
    (F : RicciFlow n M J) (T : ℝ) (representative : M × ℝ → ℝ)
    (τ : ℝ) (q : M) : ℝ :=
  let b := (F.metric (T - τ)).orthonormalBasis q
  ∑ i, (mvfderiv (𝓡 n)
    (fun x ↦ representative (x, τ)) q (b i)) ^ 2

noncomputable def reducedLengthLaplacian {J : Set ℝ}
    (F : RicciFlow n M J) (T : ℝ) (representative : M × ℝ → ℝ)
    (τ : ℝ) (q : M) : ℝ :=
  (F.connection (T - τ)).laplacian (fun x ↦ representative (x, τ)) q

structure ReducedLengthRegularPoint {J : Set ℝ} (F : RicciFlow n M J)
    (T τmax : ℝ) (p q : M) (τ : ℝ) where
  tau_pos : 0 < τ
  tau_lt : τ < τmax
  path : BackwardTimePath F T 0 τ
  path_start : path.curve 0 = p
  path_end : path.curve τ = q
  minimizing : IsMinimizingBackwardLPath F T 0 τ path
  path_realizes_reduced_length :
    reducedLength F T p q τ =
      backwardLLength F T 0 τ path.curve / (2 * Real.sqrt τ)
  unique_minimizing_path :
    ∀ q' : BackwardTimePath F T 0 τ,
      q'.curve 0 = p → q'.curve τ = q →
      IsMinimizingBackwardLPath F T 0 τ q' →
        Set.EqOn q'.curve path.curve (Set.Icc 0 τ)
  neighborhood : Set (M × ℝ)
  neighborhood_open : IsOpen neighborhood
  center_mem : (q, τ) ∈ neighborhood
  representative : M × ℝ → ℝ
  representative_eq : ∀ z ∈ neighborhood,
    representative z = reducedLength F T p z.1 z.2
  representative_spacetime_smooth :
    ContMDiffAt ((𝓡 n).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, ℝ)) ∞
      representative (q, τ)
  representative_space_smooth_on :
    ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ)) ∞
      (fun x ↦ representative (x, τ))
      {x | (x, τ) ∈ neighborhood}
  representative_space_smooth :
    ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞
      (fun x ↦ representative (x, τ)) q
  representative_time_derivative : ∃ d : ℝ,
    HasDerivAt (fun s ↦ representative (q, s)) d τ
  path_scalar_time_derivative : ℝ → ℝ
  path_scalar_time_derivative_spec :
    ∀ s, s ∈ Set.Ioo 0 τ →
      HasDerivWithinAt
        (fun r ↦ (F.connection (T - r)).scalarCurvature (path.curve s))
        (path_scalar_time_derivative s) (Set.Icc 0 τ) s
  harnack_integrable :
    IntervalIntegrable
      (fun s ↦ s * Real.sqrt s * reducedHarnackDensity F T path.curve
        path_scalar_time_derivative s) MeasureTheory.volume 0 τ

structure ReducedLengthUpperBarrier {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (p q : M) (τ : ℝ) where
  neighborhood : Set (M × ℝ)
  neighborhood_open : IsOpen neighborhood
  center_mem : (q, τ) ∈ neighborhood
  representative : M × ℝ → ℝ
  touches : representative (q, τ) = reducedLength F T p q τ
  dominates : ∀ z ∈ neighborhood,
    reducedLength F T p z.1 z.2 ≤ representative z
  representative_spacetime_smooth :
    ContMDiffAt ((𝓡 n).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, ℝ)) ∞
      representative (q, τ)
  representative_space_smooth_on :
    ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ)) ∞
      (fun x ↦ representative (x, τ))
      {x | (x, τ) ∈ neighborhood}
  representative_space_smooth :
    ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞
      (fun x ↦ representative (x, τ)) q
  representative_time_derivative : ∃ d : ℝ,
    HasDerivAt (fun s ↦ representative (q, s)) d τ

noncomputable def reducedLengthBarrierResidual {J : Set ℝ}
    (F : RicciFlow n M J) (T : ℝ) (p q : M) (τ : ℝ)
    (B : ReducedLengthUpperBarrier F T p q τ) : ℝ :=
  deriv (fun s ↦ B.representative (q, s)) τ +
    reducedLengthLaplacian F T B.representative τ q -
      ((n : ℝ) / 2 - B.representative (q, τ)) / τ

structure LExponentialFamily {J : Set ℝ} (F : RicciFlow n M J)
    (T τmax : ℝ) (p : M) where
  gamma : TangentSpace (𝓡 n) p → ℝ → M
  gamma_at_zero : ∀ Z, gamma Z 0 = p
  path : ∀ (_Z : TangentSpace (𝓡 n) p) b, 0 < b → b < τmax → BackwardTimePath F T 0 b
  path_eq : ∀ Z b (hb : 0 < b) (hmax : b < τmax),
    (path Z b hb hmax).curve = gamma Z
  regularization : ∀ Z b (hb : 0 < b) (hmax : b < τmax),
    RegularizedLGeodesicData (path Z b hb hmax)
  squareFamily : TangentSpace (𝓡 n) p → ℝ → M
  squareDomain : Set (TangentSpace (𝓡 n) p × ℝ)
  square_open : IsOpen squareDomain
  square_contains :
    Set.univ ×ˢ Set.Ico 0 (Real.sqrt τmax) ⊆ squareDomain
  square_smooth :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric T).toRiemannianMetric⟩
    ContMDiffOn ((𝓘(ℝ, TangentSpace (𝓡 n) p)).prod (𝓘(ℝ, ℝ))) (𝓡 n) ∞
      (fun z ↦ squareFamily z.1 z.2) squareDomain
  square_agrees : ∀ Z s, s ∈ Set.Ico 0 (Real.sqrt τmax) →
    squareFamily Z s = gamma Z (s ^ 2)
  square_at_zero : ∀ Z, squareFamily Z 0 = p
  initial_derivative : ∀ Z,
    (square_at_zero Z) ▸ curveVelocity (squareFamily Z) 0 = (2 : ℝ) • Z
  gamma_smooth :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric T).toRiemannianMetric⟩
    ContMDiffOn ((𝓘(ℝ, TangentSpace (𝓡 n) p)).prod (𝓘(ℝ, ℝ))) (𝓡 n) ∞
      (fun z ↦ gamma z.1 z.2) (Set.univ ×ˢ Set.Ioo 0 τmax)

noncomputable def LExponentialFamily.action {J : Set ℝ} {F : RicciFlow n M J}
    {T τmax : ℝ} {p : M} (E : LExponentialFamily F T τmax p)
    (Z : TangentSpace (𝓡 n) p) (τ : ℝ) : ℝ :=
  backwardLLength F T 0 τ (E.gamma Z)

noncomputable def LExponentialFamily.sliceDifferential {J : Set ℝ}
    {F : RicciFlow n M J} {T τmax : ℝ} {p : M}
    (E : LExponentialFamily F T τmax p)
    (Z : TangentSpace (𝓡 n) p) (τ : ℝ) :
    TangentSpace (𝓡 n) p →L[ℝ] TangentSpace (𝓡 n) (E.gamma Z τ) :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  mfderiv (𝓘(ℝ, TangentSpace (𝓡 n) p)) (𝓡 n) (fun V ↦ E.gamma V τ) Z

def LExponentialFamily.uniqueMinimizing {J : Set ℝ} {F : RicciFlow n M J}
    {T τmax : ℝ} {p : M} (E : LExponentialFamily F T τmax p)
    (Z : TangentSpace (𝓡 n) p) (τ : ℝ) : Prop :=
  ∃ (hτ : 0 < τ) (hmax : τ < τmax),
    IsMinimizingBackwardLPath F T 0 τ (E.path Z τ hτ hmax) ∧
    ∀ q : BackwardTimePath F T 0 τ,
      q.curve 0 = p → q.curve τ = E.gamma Z τ →
      IsMinimizingBackwardLPath F T 0 τ q →
        Set.EqOn q.curve (E.gamma Z) (Set.Icc 0 τ)

def LExponentialFamily.regularDomain {J : Set ℝ} {F : RicciFlow n M J}
    {T τmax : ℝ} {p : M} (E : LExponentialFamily F T τmax p) :
    Set (TangentSpace (𝓡 n) p × ℝ) :=
  {z | E.uniqueMinimizing z.1 z.2 ∧
    Function.Bijective (E.sliceDifferential z.1 z.2)}

def LExponentialFamily.localRegularDomain {J : Set ℝ} {F : RicciFlow n M J}
    {T τmax : ℝ} {p : M} (E : LExponentialFamily F T τmax p) :
    Set (TangentSpace (𝓡 n) p × ℝ) :=
  {z | 0 < z.2 ∧ z.2 < τmax ∧
    Function.Bijective (E.sliceDifferential z.1 z.2) ∧
    ∃ N : Set (TangentSpace (𝓡 n) p),
      IsOpen N ∧ z.1 ∈ N ∧ ∀ Z ∈ N, E.uniqueMinimizing Z z.2}

structure LExponentialGeometry {J : Set ℝ} (F : RicciFlow n M J)
    (T τmax : ℝ) (p : M) extends LExponentialFamily F T τmax p where
  action_smooth :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric T).toRiemannianMetric⟩
    ContDiffOn ℝ ∞
      (fun z : TangentSpace (𝓡 n) p × ℝ ↦ toLExponentialFamily.action z.1 z.2)
      (Set.univ ×ˢ Set.Ioo 0 τmax)
  action_initial_differential :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric T).toRiemannianMetric⟩
    ∀ Z τ, 0 < τ → τ < τmax → ∀ W : TangentSpace (𝓡 n) p,
      fderiv ℝ (fun V ↦ toLExponentialFamily.action V τ) Z W =
        2 * Real.sqrt τ * (F.metric (T - τ)).inner (gamma Z τ)
          (curveVelocity (gamma Z) τ) (toLExponentialFamily.sliceDifferential Z τ W)
  action_time_derivative :
    ∀ Z τ, 0 < τ → τ < τmax →
      HasDerivAt (fun s ↦ toLExponentialFamily.action Z s)
        (backwardLIntegrand F T (gamma Z) τ) τ
  jacobi_differential :
    ∀ (Z W : TangentSpace (𝓡 n) p) b (hb : 0 < b) (hmax : b < τmax),
      ∃ Y : ∀ τ, TangentSpace (𝓡 n) ((path Z b hb hmax).curve τ),
        IsLJacobiField F T 0 b (path Z b hb hmax) Y ∧
        HasLJacobiInitialDerivative (regularization Z b hb hmax) Y
          (((congrFun (path_eq Z b hb hmax) 0).trans (gamma_at_zero Z)).symm ▸
            ((2 : ℝ) • W)) ∧
        ∀ τ ∈ Set.Icc 0 b,
          ((congrFun (path_eq Z b hb hmax) τ) ▸ Y τ : TangentSpace (𝓡 n) (gamma Z τ)) =
            toLExponentialFamily.sliceDifferential Z τ W
  minimizers_lift :
    ∀ τ (_hτ : 0 < τ) (_hmax : τ < τmax), ∀ q : BackwardTimePath F T 0 τ,
      q.curve 0 = p → IsMinimizingBackwardLPath F T 0 τ q →
        ∃! Z : TangentSpace (𝓡 n) p, Set.EqOn q.curve (gamma Z) (Set.Icc 0 τ)
  minimizing_initial_bounded :
    ∀ Q : Set (M × ℝ), IsCompact Q → Q ⊆ Set.univ ×ˢ Set.Ioo 0 τmax →
      ∃ A : ℝ, 0 ≤ A ∧
        ∀ Z τ (hτ : 0 < τ) (hmax : τ < τmax),
          (gamma Z τ, τ) ∈ Q →
          IsMinimizingBackwardLPath F T 0 τ (path Z τ hτ hmax) →
            (F.metric T).tangentNorm p Z ≤ A
  regular_chart : OpenPartialHomeomorph (TangentSpace (𝓡 n) p × ℝ) (M × ℝ)
  regular_source : regular_chart.source = toLExponentialFamily.regularDomain
  regular_forward : ∀ z, regular_chart z = (gamma z.1 z.2, z.2)
  regular_forward_smooth :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric T).toRiemannianMetric⟩
    ContMDiffOn ((𝓘(ℝ, TangentSpace (𝓡 n) p)).prod (𝓘(ℝ, ℝ)))
      ((𝓡 n).prod (𝓘(ℝ, ℝ))) ∞ regular_chart regular_chart.source
  regular_inverse_smooth :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric T).toRiemannianMetric⟩
    ContMDiffOn ((𝓡 n).prod (𝓘(ℝ, ℝ)))
      ((𝓘(ℝ, TangentSpace (𝓡 n) p)).prod (𝓘(ℝ, ℝ))) ∞
      regular_chart.symm regular_chart.target
  regular_target_times : regular_chart.target ⊆ Set.univ ×ˢ Set.Ioo 0 τmax
  regular_inverse_time :
    ∀ z ∈ regular_chart.target, (regular_chart.symm z).2 = z.2
  regular_domain_eq_local :
    toLExponentialFamily.regularDomain = toLExponentialFamily.localRegularDomain
  regular_point : ∀ z ∈ regular_chart.target,
    ReducedLengthRegularPoint F T τmax p z.1 z.2
  regular_point_path : ∀ z (hz : z ∈ regular_chart.target),
    Set.EqOn (regular_point z hz).path.curve
      (gamma (regular_chart.symm z).1) (Set.Icc 0 z.2)
  regular_point_neighborhood : ∀ z (hz : z ∈ regular_chart.target),
    (regular_point z hz).neighborhood ⊆ regular_chart.target
  regular_point_representative : ∀ z (hz : z ∈ regular_chart.target),
    (regular_point z hz).representative =
      fun w ↦ toLExponentialFamily.action (regular_chart.symm w).1 w.2 /
        (2 * Real.sqrt w.2)
  backward_nesting :
    ∀ Z τ₂, (Z, τ₂) ∈ toLExponentialFamily.regularDomain →
      ∀ τ₁, 0 < τ₁ → τ₁ ≤ τ₂ →
        (Z, τ₁) ∈ toLExponentialFamily.regularDomain
  bounded_initial_coverage :
    ∀ A : ℝ, 0 ≤ A → ∃ δ : ℝ, 0 < δ ∧ δ < τmax ∧
      ∀ Z : TangentSpace (𝓡 n) p, (F.metric T).tangentNorm p Z ≤ A →
        ∀ τ, 0 < τ → τ < δ → (Z, τ) ∈ toLExponentialFamily.regularDomain

def LExponentialGeometry.regularImage {J : Set ℝ} {F : RicciFlow n M J}
    {T τmax : ℝ} {p : M} (G : LExponentialGeometry F T τmax p) : Set (M × ℝ) :=
  G.regular_chart.target

noncomputable def LExponentialGeometry.representative {J : Set ℝ}
    {F : RicciFlow n M J} {T τmax : ℝ} {p : M}
    (G : LExponentialGeometry F T τmax p) (z : M × ℝ) : ℝ :=
  G.toLExponentialFamily.action (G.regular_chart.symm z).1 z.2 /
    (2 * Real.sqrt z.2)

end PoincareConjecture
