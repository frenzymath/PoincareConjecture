import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.WeakComparison
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Linearity

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology
open Poincare.Riemannian.Soul

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [MetricSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  {g : RiemannianMetric 3 M}

theorem integral_busemann_transition_difference_eq_restricted
    (D : LeviCivitaData g)
    {ray : ℝ → M}
    (N₁ N₂ : EpsilonNeck g) (T₁ T₂ : M → ℝ)
    (hT₁ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ T₁)
    (hT₂ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ T₂)
    (hzero₁ : ∀ x ∉ N₁.carrier, D.gradient T₁ x = 0)
    (hzero₂ : ∀ x ∉ N₂.carrier, D.gradient T₂ x = 0)
    (hneck : Disjoint N₁.carrier N₂.carrier)
    (hI₁ : Integrable (fun x => mvfderiv (𝓡 3) (busemann ray) x
      (D.gradient T₁ x)) g.volumeMeasure)
    (hI₂ : Integrable (fun x => mvfderiv (𝓡 3) (busemann ray) x
      (D.gradient T₂ x)) g.volumeMeasure) :
    (∫ x, mvfderiv (𝓡 3) (busemann ray) x
      (D.gradient (fun y => T₁ y - T₂ y) x) ∂g.volumeMeasure) =
      (∫ x in N₁.carrier, mvfderiv (𝓡 3) (busemann ray) x
        (D.gradient T₁ x) ∂g.volumeMeasure) -
      (∫ x in N₂.carrier, mvfderiv (𝓡 3) (busemann ray) x
        (D.gradient T₂ x) ∂g.volumeMeasure) := by
  let F₁ : M → ℝ := fun x => mvfderiv (𝓡 3) (busemann ray) x
    (D.gradient T₁ x)
  let F₂ : M → ℝ := fun x => mvfderiv (𝓡 3) (busemann ray) x
    (D.gradient T₂ x)
  have hgrad_neg (x : M) : D.gradient (fun y => -T₂ y) x = -D.gradient T₂ x := by
    apply (g.inner_isInvertible x).injective
    ext v
    calc
      g.inner x (D.gradient (fun y => -T₂ y) x) v =
          mvfderiv (𝓡 3) (fun y => -T₂ y) x v := D.inner_gradient _ _ _
      _ = -mvfderiv (𝓡 3) T₂ x v := by
        rw [mvfderiv_fun_neg]
        rfl
      _ = -(g.inner x (D.gradient T₂ x) v) := by rw [D.inner_gradient]
      _ = g.inner x (-D.gradient T₂ x) v := by simp
  have hgrad_sub (x : M) :
      D.gradient (fun y => T₁ y - T₂ y) x = D.gradient T₁ x - D.gradient T₂ x := by
    have hsum := D.gradient_add
      ((hT₁ x).mdifferentiableAt (by simp))
      ((hT₂.neg x).mdifferentiableAt (by simp))
    rw [show (fun y => T₁ y - T₂ y) = (fun y => T₁ y + -T₂ y) by
      funext y; ring, hsum, hgrad_neg]
    simp only [sub_eq_add_neg]
  have hflux : ∀ x, F₁ x - F₂ x =
      mvfderiv (𝓡 3) (busemann ray) x
        (D.gradient (fun y => T₁ y - T₂ y) x) := by
    intro x
    rw [hgrad_sub]
    simp only [F₁, F₂, map_sub]
  have hpoint : ∀ x, F₁ x - F₂ x =
      N₁.carrier.indicator F₁ x - N₂.carrier.indicator F₂ x := by
    intro x
    by_cases hx₁ : x ∈ N₁.carrier
    · have hx₂ : x ∉ N₂.carrier := fun hx => Set.disjoint_left.mp hneck hx₁ hx
      have hz₂ : F₂ x = 0 := by simp [F₂, hzero₂ x hx₂]
      rw [Set.indicator_of_mem hx₁, Set.indicator_of_notMem hx₂]
      rw [hz₂]
    · by_cases hx₂ : x ∈ N₂.carrier
      · have hz₁ : F₁ x = 0 := by simp [F₁, hzero₁ x hx₁]
        rw [Set.indicator_of_notMem hx₁, Set.indicator_of_mem hx₂]
        rw [hz₁]
      · have hz₁ : F₁ x = 0 := by simp [F₁, hzero₁ x hx₁]
        have hz₂ : F₂ x = 0 := by simp [F₂, hzero₂ x hx₂]
        rw [Set.indicator_of_notMem hx₁, Set.indicator_of_notMem hx₂]
        rw [hz₁, hz₂]
  have hI₁' : Integrable (N₁.carrier.indicator F₁) g.volumeMeasure :=
    hI₁.indicator N₁.carrier_open.measurableSet
  have hI₂' : Integrable (N₂.carrier.indicator F₂) g.volumeMeasure :=
    hI₂.indicator N₂.carrier_open.measurableSet
  calc
    ∫ x, mvfderiv (𝓡 3) (busemann ray) x
        (D.gradient (fun y => T₁ y - T₂ y) x) ∂g.volumeMeasure =
      ∫ x, F₁ x - F₂ x ∂g.volumeMeasure := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact (hflux x).symm
    _ = ∫ x, N₁.carrier.indicator F₁ x -
        N₂.carrier.indicator F₂ x ∂g.volumeMeasure := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact hpoint x
    _ = (∫ x, N₁.carrier.indicator F₁ x ∂g.volumeMeasure) -
        (∫ x, N₂.carrier.indicator F₂ x ∂g.volumeMeasure) :=
      integral_sub hI₁' hI₂'
    _ = (∫ x in N₁.carrier, F₁ x ∂g.volumeMeasure) -
        (∫ x in N₂.carrier, F₂ x ∂g.volumeMeasure) := by
      rw [integral_indicator N₁.carrier_open.measurableSet,
        integral_indicator N₂.carrier_open.measurableSet]

theorem integrable_busemann_axialTransition_flux
    [ConnectedSpace M] (D : LeviCivitaData g) (hc : MetricComplete g)
    (hdist : ∀ x y : M, dist x y = (g.edist x y).toReal)
    (hm : D.NonnegativeRicciCurvature)
    {ray : ℝ → M} (hray : IsRay ray)
    (N : EpsilonNeck g) {A B : Set M} {φ : ℝ → ℝ}
    (hA : IsOpen A) (hB : IsOpen B)
    (hdisj : Disjoint A B) (hcover : A ∪ B = N.central_sphereᶜ)
    (hneg : N.region (-N.epsilon⁻¹) 0 ⊆ A)
    (hpos : N.region 0 N.epsilon⁻¹ ⊆ B)
    {L : ℝ} (hL : 0 < L) (hLe : L < N.epsilon⁻¹)
    (hφ : ContDiff ℝ ∞ φ)
    (hφ_range : ∀ s, φ s ∈ Icc 0 1)
    (hzero : ∀ s ≤ -L, φ s = 0)
    (hone : ∀ s, L ≤ s → φ s = 1)
    (hAc : IsCompact (closure A)) :
    Integrable (fun x => mvfderiv (𝓡 3) (busemann ray) x
      (D.gradient (N.axialTransition A φ) x)) g.volumeMeasure := by
  have hT := N.contMDiff_axialTransition hA hB hdisj hcover hneg hpos
    hL hLe hφ hzero hone
  have hcompact := N.hasCompactSupport_one_sub_axialTransition hAc hdisj
    hcover hneg hL hLe hone
  have hnonneg : ∀ x, 0 ≤ 1 - N.axialTransition A φ x := by
    intro x
    exact sub_nonneg.mpr (N.axialTransition_mem_Icc hφ_range x).2
  obtain ⟨hI, _⟩ := g.ray_busemann_integral_differential_nonneg D (by norm_num)
    hc hm hdist hray (fun x => 1 - N.axialTransition A φ x)
    (contMDiff_const.sub hT) hcompact hnonneg
  have hgrad_one_sub (x : M) :
      D.gradient (fun y => 1 - N.axialTransition A φ y) x =
        -D.gradient (N.axialTransition A φ) x := by
    apply (g.inner_isInvertible x).injective
    ext v
    calc
      g.inner x (D.gradient (fun y => 1 - N.axialTransition A φ y) x) v =
          mvfderiv (𝓡 3) (fun y => 1 - N.axialTransition A φ y) x v :=
        D.inner_gradient _ _ _
      _ = mvfderiv (𝓡 3) (fun _ : M => (1 : ℝ)) x v -
          mvfderiv (𝓡 3) (N.axialTransition A φ) x v := by
        rw [mvfderiv_fun_sub mdifferentiableAt_const
          ((hT x).mdifferentiableAt (by simp))]
        simp only [sub_apply]
      _ = -mvfderiv (𝓡 3) (N.axialTransition A φ) x v := by
        rw [mvfderiv_const]
        simp
      _ = -(g.inner x (D.gradient (N.axialTransition A φ) x) v) := by
        rw [D.inner_gradient]
      _ = g.inner x (-D.gradient (N.axialTransition A φ) x) v := by simp
  apply hI.neg.congr
  filter_upwards [] with x
  change -mvfderiv (𝓡 3) (busemann ray) x
      (D.gradient (fun y => 1 - N.axialTransition A φ y) x) =
    mvfderiv (𝓡 3) (busemann ray) x
      (D.gradient (N.axialTransition A φ) x)
  rw [hgrad_one_sub]
  simp

end PoincareConjecture.EpsilonNeck
