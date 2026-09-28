import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.MetricExpansion.Flow
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.MetricExpansion.Variation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.Transport.Shift

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem inner_connection_boundedNormalizedGradient_of_tangent
    (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (ha : ∀ y, a < f y → 1 ≤ g.inner y (D.gradient f y) (D.gradient f y))
    {x : M} (hx : a < f x) (v : TangentSpace (𝓡 n) x)
    (hv : mvfderiv (𝓡 n) f x v = 0) :
    g.inner x (D.connection (D.boundedNormalizedGradient f) x v) v =
      D.hessian f x v v / g.inner x (D.gradient f x) (D.gradient f x) := by
  have hq : 0 < g.inner x (D.gradient f x) (D.gradient f x) := lt_of_lt_of_le
    (by norm_num) (ha x hx)
  have hn : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (T% (D.normalizedGradient f)) x :=
    ((contDiffAt_inv ℝ hq.ne').contMDiffAt.comp x
      (g.contMDiff_inner_gradient hf hf x)).smul_section (D.contMDiffAt_gradient (hf x))
  have heq : D.boundedNormalizedGradient f =ᶠ[𝓝 x] D.normalizedGradient f := by
    filter_upwards [(isOpen_lt continuous_const hf.continuous).mem_nhds hx] with y hy
    exact D.boundedNormalizedGradient_eq f y (ha y hy)
  have hc := D.connection.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    ((D.contMDiff_boundedNormalizedGradient hf x).mdifferentiableAt (by simp))
    (hn.mdifferentiableAt (by simp)) (by simp) heq
  rw [congrArg (fun L => L v) hc]
  exact D.inner_connection_normalizedGradient_of_tangent (hf x) hq.ne' v hv

omit [IsManifold (𝓡 n) ∞ M] in

theorem flow_preserves_potential_differential_of_shift
    {f : M → ℝ} {Φ : ℝ → M → M}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hs : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ (Function.uncurry Φ))
    {x : M} {t : ℝ}
    (hshift : (fun y => f (Φ t y)) =ᶠ[𝓝 x] fun y => f y + t)
    (v : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) f (Φ t x) (mfderiv (𝓡 n) (𝓡 n) (Φ t) x v) =
      mvfderiv (𝓡 n) f x v := by
  have hF : ContMDiff (𝓡 n) (𝓡 n) ∞ (Φ t) :=
    hs.comp (contMDiff_const.prodMk contMDiff_id)
  have hc := mvfderiv_comp x ((hf _).mdifferentiableAt (by simp))
    ((hF x).mdifferentiableAt (by simp))
  have he : mvfderiv (𝓡 n) (f ∘ Φ t) x =
      mvfderiv (𝓡 n) (fun y => f y + t) x := by
    have heq : (f ∘ Φ t) =ᶠ[𝓝 x] (fun y => f y + t) := hshift
    unfold mvfderiv
    rw [heq.mfderiv_eq (I := 𝓡 n) (I' := 𝓘(ℝ, ℝ)), heq.eq_of_nhds]
  rw [he, mvfderiv_fun_add ((hf x).mdifferentiableAt (by simp))
    mdifferentiableAt_const, mvfderiv_const, add_zero] at hc
  exact (congrArg (fun L => L v) hc).symm

theorem hasDerivAt_boundedNormalizedGradient_flow_squared_length
    (D : LeviCivitaData g) {f : M → ℝ} {Φ : ℝ → M → M}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hs : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ (Function.uncurry Φ))
    (hΦ : ∀ x, IsMIntegralCurve (I := 𝓡 n) (fun t => Φ t x)
      (D.boundedNormalizedGradient f))
    {a : ℝ} (ha : ∀ y, a < f y → 1 ≤ g.inner y (D.gradient f y) (D.gradient f y))
    (x : M) (v : TangentSpace (𝓡 n) x) (t : ℝ) (hx : a < f (Φ t x))
    (htan : mvfderiv (𝓡 n) f (Φ t x) (mfderiv (𝓡 n) (𝓡 n) (Φ t) x v) = 0) :
    let w := mfderiv (𝓡 n) (𝓡 n) (Φ t) x v
    HasDerivAt (fun s => g.inner (Φ s x)
      (mfderiv (𝓡 n) (𝓡 n) (Φ s) x v) (mfderiv (𝓡 n) (𝓡 n) (Φ s) x v))
      (2 * D.hessian f (Φ t x) w w /
        g.inner (Φ t x) (D.gradient f (Φ t x)) (D.gradient f (Φ t x))) t := by
  have hd := D.hasDerivAt_manifoldFlow_squared_length
    (D.contMDiff_boundedNormalizedGradient hf) hs hΦ x v t
  dsimp only at hd ⊢
  rw [D.inner_connection_boundedNormalizedGradient_of_tangent hf ha hx _ htan] at hd
  convert! hd using 1
  ring

theorem boundedNormalizedGradient_flow_squared_length_monotoneOn
    (D : LeviCivitaData g) {f : M → ℝ} {Φ : ℝ → M → M}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hs : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ (Function.uncurry Φ))
    (hΦ : ∀ x, IsMIntegralCurve (I := 𝓡 n) (fun t => Φ t x)
      (D.boundedNormalizedGradient f))
    {a : ℝ} (ha : ∀ y, a < f y → 1 ≤ g.inner y (D.gradient f y) (D.gradient f y))
    (hhess : ∀ y, a < f y → ∀ w : TangentSpace (𝓡 n) y,
      mvfderiv (𝓡 n) f y w = 0 → 0 ≤ D.hessian f y w w)
    {x : M} (v : TangentSpace (𝓡 n) x) (hv : mvfderiv (𝓡 n) f x v = 0)
    {s t : ℝ} (hhigh : ∀ r ∈ Icc s t, a < f (Φ r x))
    (hshift : ∀ r ∈ Icc s t,
      (fun y => f (Φ r y)) =ᶠ[𝓝 x] fun y => f y + r) :
    MonotoneOn (fun r => g.inner (Φ r x)
      (mfderiv (𝓡 n) (𝓡 n) (Φ r) x v) (mfderiv (𝓡 n) (𝓡 n) (Φ r) x v)) (Icc s t) := by
  have htan (r : ℝ) (hr : r ∈ Icc s t) : mvfderiv (𝓡 n) f (Φ r x)
      (mfderiv (𝓡 n) (𝓡 n) (Φ r) x v) = 0 :=
    (flow_preserves_potential_differential_of_shift hf hs (hshift r hr) v).trans hv
  have hd (r : ℝ) (hr : r ∈ Icc s t) :=
    D.hasDerivAt_boundedNormalizedGradient_flow_squared_length hf hs hΦ ha x v r
      (hhigh r hr) (htan r hr)
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    (fun r hr => (hd r hr).continuousAt.continuousWithinAt)
    (fun r hr => (hd r (interior_subset hr)).differentiableAt.differentiableWithinAt)
  intro r hr
  rw [(hd r (interior_subset hr)).deriv]
  exact div_nonneg (mul_nonneg (by norm_num)
    (hhess _ (hhigh r (interior_subset hr)) _ (htan r (interior_subset hr))))
    ((by norm_num : (0 : ℝ) ≤ 1).trans (ha _ (hhigh r (interior_subset hr))))

theorem boundedNormalizedGradient_flow_expands_level_metric
    (D : LeviCivitaData g) {f : M → ℝ} {Φ : ℝ → M → M}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hs : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ (Function.uncurry Φ))
    (h0 : ∀ x, Φ 0 x = x)
    (hΦ : ∀ x, IsMIntegralCurve (I := 𝓡 n) (fun t => Φ t x)
      (D.boundedNormalizedGradient f))
    {a : ℝ} (ha : ∀ y, a < f y → 1 ≤ g.inner y (D.gradient f y) (D.gradient f y))
    (hhess : ∀ y, a < f y → ∀ w : TangentSpace (𝓡 n) y,
      mvfderiv (𝓡 n) f y w = 0 → 0 ≤ D.hessian f y w w)
    {x : M} (hx : a < f x) (v : TangentSpace (𝓡 n) x)
    (hv : mvfderiv (𝓡 n) f x v = 0) {t : ℝ} (ht : 0 ≤ t) :
    g.inner x v v ≤ g.inner (Φ t x)
      (mfderiv (𝓡 n) (𝓡 n) (Φ t) x v) (mfderiv (𝓡 n) (𝓡 n) (Φ t) x v) := by
  have hlevel (y : M) (hy : a < f y) (r : ℝ) (hr : 0 ≤ r) : f (Φ r y) = f y + r := by
    have he := D.potential_boundedNormalizedGradient_eq_add hf (hΦ y) ha
      (by simpa only [h0] using hy) (show a < f (Φ 0 y) + r by rw [h0]; linarith)
    simpa only [h0] using he
  have hm := D.boundedNormalizedGradient_flow_squared_length_monotoneOn hf hs hΦ ha hhess v hv
    (s := 0) (t := t)
    (fun r hr => by rw [hlevel x hx r hr.1]; linarith [hr.1])
    (fun r hr => by
      filter_upwards [(isOpen_lt continuous_const hf.continuous).mem_nhds hx] with y hy
      exact hlevel y hy r hr.1)
  have hb := hm ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
  dsimp only at hb
  have hfun : Φ 0 = id := funext h0
  rw [hfun, mfderiv_id] at hb
  exact hb

end PoincareConjecture.LeviCivitaData
