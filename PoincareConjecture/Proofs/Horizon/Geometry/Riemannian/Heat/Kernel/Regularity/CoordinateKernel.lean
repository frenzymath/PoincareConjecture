import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Kernel.Pointwise.Smooth
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion.Spectral
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion.Supremum

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData.Dirichlet

variable {n d : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "F" => EuclideanSpace ℝ (Fin d)

def coordinateKernelDomain (T : F →L[ℝ] ℝ) (X Y : F →L[ℝ] E)
    (e₁ e₂ : OpenPartialHomeomorph E M) : Set F :=
  {z | 0 < T z ∧ X z ∈ e₁.source ∧ Y z ∈ e₂.source}

omit [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace E M] [IsManifold (𝓡 n) ∞ M] in
theorem isOpen_coordinateKernelDomain (T : F →L[ℝ] ℝ) (X Y : F →L[ℝ] E)
    (e₁ e₂ : OpenPartialHomeomorph E M) :
    IsOpen (coordinateKernelDomain T X Y e₁ e₂) :=
  (isOpen_lt continuous_const T.continuous).inter
    ((e₁.open_source.preimage X.continuous).inter (e₂.open_source.preimage Y.continuous))

def coordinateHeatKernel [NeZero n] (D : LeviCivitaData g)
    {Ω : Set M} (S : Poincare.Manifold.SmoothDomain n Ω)
    (T : F →L[ℝ] ℝ) (X Y : F →L[ℝ] E)
    (e₁ e₂ : OpenPartialHomeomorph E M) : F → ℝ :=
  fun z => heatKernelContinuousTime D S (T z) (e₁ (X z)) (e₂ (Y z))

def coordinateExhaustionKernel [NeZero n] (D : LeviCivitaData g)
    {Ω : ℕ → Set M} (S : ∀ q, Poincare.Manifold.SmoothDomain n (Ω q))
    (T : F →L[ℝ] ℝ) (X Y : F →L[ℝ] E)
    (e₁ e₂ : OpenPartialHomeomorph E M) : F → ℝ :=
  fun z => dirichletExhaustionKernel (fun q => heatKernelContinuousTime D (S q))
    (T z) (e₁ (X z)) (e₂ (Y z))

theorem contDiffAt_coordinateHeatKernel [NeZero n] (D : LeviCivitaData g)
    {Ω : Set M} (S : Poincare.Manifold.SmoothDomain n Ω)
    (T : F →L[ℝ] ℝ) (X Y : F →L[ℝ] E)
    (e₁ e₂ : OpenPartialHomeomorph E M)
    (he₁ : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e₁ e₁.source)
    (he₂ : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e₂ e₂.source)
    {z : F} (hz : z ∈ coordinateKernelDomain T X Y e₁ e₂)
    (hxΩ : e₁ (X z) ∈ Ω) (hyΩ : e₂ (Y z) ∈ Ω) :
    ContDiffAt ℝ ∞ (coordinateHeatKernel D S T X Y e₁ e₂) z := by
  have hX : ContMDiffAt (𝓡 d) (𝓡 n) ∞ (fun w => e₁ (X w)) z :=
    (he₁.contMDiffAt (e₁.open_source.mem_nhds hz.2.1)).comp z
      X.contDiff.contMDiff.contMDiffAt
  have hY : ContMDiffAt (𝓡 d) (𝓡 n) ∞ (fun w => e₂ (Y w)) z :=
    (he₂.contMDiffAt (e₂.open_source.mem_nhds hz.2.2)).comp z
      Y.contDiff.contMDiff.contMDiffAt
  have hT : ContMDiffAt (𝓡 d) 𝓘(ℝ, ℝ) ∞ T z := T.contDiff.contMDiff.contMDiffAt
  have hp : ((e₁ (X z), e₂ (Y z)), T z) ∈ ((Ω ×ˢ Ω) ×ˢ Ioi (0 : ℝ)) :=
    ⟨⟨hxΩ, hyΩ⟩, hz.1⟩
  have hk := (contMDiffOn_heatKernelContinuousTime_joint D S).contMDiffAt
    (((S.isOpen.prod S.isOpen).prod isOpen_Ioi).mem_nhds hp)
  have hcomp := hk.comp z ((hX.prodMk hY).prodMk hT)
  exact contMDiffAt_iff_contDiffAt.mp hcomp

theorem contDiffOn_coordinateHeatKernel [NeZero n] (D : LeviCivitaData g)
    {Ω : Set M} (S : Poincare.Manifold.SmoothDomain n Ω)
    (T : F →L[ℝ] ℝ) (X Y : F →L[ℝ] E)
    (e₁ e₂ : OpenPartialHomeomorph E M)
    (he₁ : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e₁ e₁.source)
    (he₂ : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e₂ e₂.source)
    {V : Set F} (hV : V ⊆ coordinateKernelDomain T X Y e₁ e₂)
    (hxΩ : (fun z => e₁ (X z)) '' V ⊆ Ω)
    (hyΩ : (fun z => e₂ (Y z)) '' V ⊆ Ω) :
    ContDiffOn ℝ ∞ (coordinateHeatKernel D S T X Y e₁ e₂) V := by
  intro z hz
  exact (contDiffAt_coordinateHeatKernel D S T X Y e₁ e₂ he₁ he₂ (hV hz)
    (hxΩ (mem_image_of_mem _ hz)) (hyΩ (mem_image_of_mem _ hz))).contDiffWithinAt

theorem eventually_contDiffOn_coordinateHeatKernel [NeZero n] (D : LeviCivitaData g)
    {Ω : ℕ → Set M} (S : ∀ q, Poincare.Manifold.SmoothDomain n (Ω q))
    (hΩmono : Monotone Ω) (hcover : (⋃ q, Ω q) = univ)
    (T : F →L[ℝ] ℝ) (X Y : F →L[ℝ] E)
    (e₁ e₂ : OpenPartialHomeomorph E M)
    (he₁ : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e₁ e₁.source)
    (he₂ : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e₂ e₂.source)
    {V : Set F} (hVc : IsCompact (closure V))
    (hV : closure V ⊆ coordinateKernelDomain T X Y e₁ e₂) :
    ∀ᶠ q in atTop, ContDiffOn ℝ ∞ (coordinateHeatKernel D (S q) T X Y e₁ e₂) V := by
  have hxcont : ContinuousOn (fun z => e₁ (X z)) (closure V) :=
    e₁.continuousOn.comp X.continuous.continuousOn (fun z hz => (hV hz).2.1)
  have hycont : ContinuousOn (fun z => e₂ (Y z)) (closure V) :=
    e₂.continuousOn.comp Y.continuous.continuousOn (fun z hz => (hV hz).2.2)
  obtain ⟨q₁, hq₁⟩ := (hVc.image_of_continuousOn hxcont).elim_directed_cover Ω
    (fun q => (S q).isOpen) (by rw [hcover]; exact subset_univ _) hΩmono.directed_le
  obtain ⟨q₂, hq₂⟩ := (hVc.image_of_continuousOn hycont).elim_directed_cover Ω
    (fun q => (S q).isOpen) (by rw [hcover]; exact subset_univ _) hΩmono.directed_le
  filter_upwards [eventually_ge_atTop (max q₁ q₂)] with q hq
  apply contDiffOn_coordinateHeatKernel D (S q) T X Y e₁ e₂ he₁ he₂
    (subset_closure.trans hV)
  · exact (image_mono subset_closure).trans
      (hq₁.trans (hΩmono ((le_max_left _ _).trans hq)))
  · exact (image_mono subset_closure).trans
      (hq₂.trans (hΩmono ((le_max_right _ _).trans hq)))

theorem locally_eventually_smooth_coordinateHeatKernel [NeZero n] (D : LeviCivitaData g)
    {Ω : ℕ → Set M} (S : ∀ q, Poincare.Manifold.SmoothDomain n (Ω q))
    (hΩmono : Monotone Ω) (hcover : (⋃ q, Ω q) = univ)
    (T : F →L[ℝ] ℝ) (X Y : F →L[ℝ] E)
    (e₁ e₂ : OpenPartialHomeomorph E M)
    (he₁ : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e₁ e₁.source)
    (he₂ : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e₂ e₂.source) :
    ∀ z ∈ coordinateKernelDomain T X Y e₁ e₂, ∃ V : Set F,
      IsOpen V ∧ z ∈ V ∧ V ⊆ coordinateKernelDomain T X Y e₁ e₂ ∧
        ∀ᶠ q in atTop, ContDiffOn ℝ ∞ (coordinateHeatKernel D (S q) T X Y e₁ e₂) V := by
  intro z hz
  obtain ⟨R, hR, hRD⟩ := Metric.isOpen_iff.mp
    (isOpen_coordinateKernelDomain T X Y e₁ e₂) z hz
  have hVD : closure (Metric.ball z (R / 2)) ⊆ coordinateKernelDomain T X Y e₁ e₂ :=
    Metric.closure_ball_subset_closedBall.trans
      ((Metric.closedBall_subset_ball (half_lt_self hR)).trans hRD)
  have hVc : IsCompact (closure (Metric.ball z (R / 2))) :=
    (isCompact_closedBall z (R / 2)).of_isClosed_subset isClosed_closure
      Metric.closure_ball_subset_closedBall
  exact ⟨Metric.ball z (R / 2), Metric.isOpen_ball, Metric.mem_ball_self (half_pos hR),
    subset_closure.trans hVD,
    eventually_contDiffOn_coordinateHeatKernel D S hΩmono hcover T X Y e₁ e₂ he₁ he₂ hVc hVD⟩

theorem tendsto_coordinateHeatKernel [NeZero n] [PreconnectedSpace M]
    (D : LeviCivitaData g) (hc : MetricComplete g) {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x), -k * g.inner x v v ≤ D.ricci x v v)
    {Ω : ℕ → Set M} (S : ∀ q, Poincare.Manifold.SmoothDomain n (Ω q))
    (hΩmono : Monotone Ω) (hcover : (⋃ q, Ω q) = univ)
    (T : F →L[ℝ] ℝ) (X Y : F →L[ℝ] E)
    (e₁ e₂ : OpenPartialHomeomorph E M) {z : F}
    (hz : z ∈ coordinateKernelDomain T X Y e₁ e₂) :
    Tendsto (fun q => coordinateHeatKernel D (S q) T X Y e₁ e₂ z) atTop
      (𝓝 (coordinateExhaustionKernel D S T X Y e₁ e₂ z)) := by
  apply DirichletExhaustion.tendsto_supremum
    (fun t ht x y => D.monotone_heatKernelContinuousTime_exhaustion S hΩmono ht x y)
    (fun t ht x y => D.bddAbove_dirichletHeatKernel_exhaustion
      (Nat.pos_of_ne_zero (NeZero.ne n)) hc hk hRic
      (fun q => (S q).isOpen) hΩmono hcover
      (fun q => heatKernelContinuousTime_isDirichletHeatKernel D (S q))
      (fun t ht x y => D.monotone_heatKernelContinuousTime_exhaustion S hΩmono ht x y)
      ht x y) hz.1

end PoincareConjecture.LeviCivitaData.Dirichlet
