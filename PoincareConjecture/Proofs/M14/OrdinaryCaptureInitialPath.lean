import PoincareConjecture.Proofs.M14.OrdinaryCaptureInitialVelocity
import PoincareConjecture.Proofs.M14.OrdinaryCaptureValues

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {C : Type u} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
  [T3Space C] [ConnectedSpace C] [SecondCountableTopology C]
  [MeasurableSpace C] [BorelSpace C] {K : SpacetimeInterval}
  {e : CompatibleSpacetimeCylinder G.spacetime (G.timeIntervals.interval K) C}
  {g : SpacetimeCylinderMetric e} {F : RicciFlow n C K.domain} {τmax : ℝ}
  (t₀ : (G.timeIntervals.interval K).Point) (c₀ : C)
  (D : M14OrdinaryCaptureData G C K e g F t₀.val τmax)

private theorem capture_initial_path_cast {T a b : ℝ} {x y : G.Point}
    {Z : G.Horizontal x} (h : a = b) (P : M14SquareRootInitialValuePath G T a x y Z) :
    (h ▸ P : M14SquareRootInitialValuePath G T b x y Z).path.curve = P.path.curve := by
  cases h
  rfl

theorem ordinaryCapture_square_initial_velocity
    {τ : ℝ} {y : G.Point} (A : LExponentialFamily F t₀.val τmax c₀)
    (W : TangentSpace (𝓡 n) c₀)
    (p : M14BackwardPath G t₀.val 0 τ (e.toSpacetime (t₀, c₀)) y)
    (R : M14SquareRootPath G p) (hmax : τ < τmax)
    (hc : ∀ s ∈ Icc 0 τ, p.curve s ∈ range e.toSpacetime)
    (hcurve : EqOn (D.path_map 0 τ _ y p hc).curve (A.gamma W) (Icc 0 τ)) :
    ∃ h : R.curve 0 = e.toSpacetime (t₀, c₀),
      h ▸ R.horizontal_velocity 0 = (2 : ℝ) • g.spatialTangentEquiv t₀ c₀ W := by
  let q := D.path_map 0 τ _ y p hc
  let θ : ℝ → (G.timeIntervals.interval K).Point := fun s =>
    ordinaryCaptureClock (G.timeIntervals.interval K) t₀ t₀.val (s ^ 2)
  have hsq {s : ℝ} (hs : s ∈ M14SqrtParameterInterval 0 τ) : s ^ 2 ∈ Icc 0 τ := by
    have hs0 : 0 ≤ s := by simpa only [M14SqrtParameterInterval, Real.sqrt_zero] using hs.1
    refine ⟨sq_nonneg s, ?_⟩
    have hle : s ≤ Real.sqrt τ := hs.2
    nlinarith [Real.sq_sqrt p.tau_lt.le, Real.sqrt_nonneg τ]
  have hθval {s : ℝ} (hs : s ∈ M14SqrtParameterInterval 0 τ) :
      (θ s).val = t₀.val - s ^ 2 :=
    ordinaryCaptureClock_val (G.timeIntervals.interval K) t₀ t₀.val (q.time_mem _ (hsq hs))
  have hθsmooth : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡∂ 1) ∞ θ (M14SqrtParameterInterval 0 τ) := by
    apply intervalLift_contMDiffOn
    exact (contMDiff_const.sub (contMDiff_id.pow 2)).contMDiffOn.congr
      (fun _ hs => hθval hs)
  have hzero : (0 : ℝ) ∈ M14SqrtParameterInterval 0 τ := by
    simp only [M14SqrtParameterInterval, Real.sqrt_zero, mem_Icc, le_refl, true_and]
    exact Real.sqrt_nonneg τ
  apply ordinaryCapture_square_initial_velocity_of_eqOn e g t₀ c₀ A W p R hmax θ
    (by simpa only [θ, zero_pow (by decide : 2 ≠ 0)] using
      ordinaryCaptureClock_zero (G.timeIntervals.interval K) t₀)
    ((hθsmooth 0 hzero).mdifferentiableWithinAt (by simp))
  intro s hs
  have hs0 : 0 ≤ s := by simpa only [M14SqrtParameterInterval, Real.sqrt_zero] using hs.1
  have hclock : (⟨t₀.val - s ^ 2, q.time_mem _ (hsq hs)⟩ :
      (G.timeIntervals.interval K).Point) = θ s := Subtype.ext (hθval hs).symm
  have hsmax : s < Real.sqrt τmax := hs.2.trans_lt (Real.sqrt_lt_sqrt p.tau_lt.le hmax)
  calc
    R.curve s = p.curve (s ^ 2) := R.agrees s hs
    _ = e.toSpacetime (⟨t₀.val - s ^ 2, q.time_mem _ (hsq hs)⟩, q.curve (s ^ 2)) :=
      (D.path_capture_eq 0 τ _ y p hc _ (hsq hs)).symm
    _ = e.toSpacetime (θ s, A.squareFamily W s) := by
      rw [hclock, hcurve (hsq hs), A.square_agrees W s ⟨hs0, hsmax⟩]

theorem ordinaryCapture_minimizing_branch_identification
    (hPath : M14PathCalculusConclusion G)
    (E : M14ExponentialFamily G t₀.val (e.toSpacetime (t₀, c₀)))
    {τ : ℝ} {y : G.Point} (A : LExponentialFamily F t₀.val τmax c₀)
    (W : TangentSpace (𝓡 n) c₀)
    (p : M14BackwardPath G t₀.val 0 τ (e.toSpacetime (t₀, c₀)) y)
    (hp : M14IsMinimizing p) (hmax : τ < τmax)
    (hc : ∀ s ∈ Icc 0 τ, p.curve s ∈ range e.toSpacetime)
    (hcurve : EqOn (D.path_map 0 τ _ y p hc).curve (A.gamma W) (Icc 0 τ)) :
    (g.spatialTangentEquiv t₀ c₀ W, Real.sqrt τ) ∈ E.domain ∧
      EqOn p.curve (fun s => E.gamma (g.spatialTangentEquiv t₀ c₀ W) (Real.sqrt s))
        (Icc 0 τ) := by
  obtain ⟨E₀, heuler⟩ := hPath.minimizer_euler _ _ _ _ _ p hp
  obtain ⟨R, S, hsquare⟩ := hPath.square_root_regularization _ _ _ _ _ p E₀ heuler
  let P : M14SquareRootInitialValuePath G t₀.val τ (e.toSpacetime (t₀, c₀)) y
      (g.spatialTangentEquiv t₀ c₀ W) :=
    { path := p
      square_path := R
      extension := S
      euler := hsquare
      initial_velocity := ordinaryCapture_square_initial_velocity t₀ c₀ D A W p R hmax hc hcurve }
  have hsq : (Real.sqrt τ) ^ 2 = τ := Real.sq_sqrt p.tau_lt.le
  let P' : M14SquareRootInitialValuePath G t₀.val ((Real.sqrt τ) ^ 2)
      (e.toSpacetime (t₀, c₀)) y (g.spatialTangentEquiv t₀ c₀ W) := hsq.symm ▸ P
  have hpos : 0 < Real.sqrt τ := Real.sqrt_pos.mpr p.tau_lt
  refine ⟨(E.positive_survival_iff _ _ hpos).mpr ⟨y, ⟨P'⟩⟩, ?_⟩
  have h := E.initial_value_agreement _ _ hpos y P'
  rw [show P'.path.curve = p.curve from capture_initial_path_cast hsq.symm P, hsq] at h
  exact h

end PoincareConjecture.M14
