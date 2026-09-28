import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Flow.Outward.DistanceAscent
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Flow.Normalization

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem strictMono_distance_of_outward_flow
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hc : MetricComplete g)
    {p : M} {X : (x : M) → TangentSpace (𝓡 n) x}
    (hX : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% X)) (hp : X p = 0)
    {a : M → ℝ} (ha : Continuous a) (hapos : ∀ y, y ≠ p → 0 < a y)
    (hpair : ∀ y : M, y ≠ p → ∀ γ : ℝ → M,
      g.IsGeodesicOn γ (Icc 0 (g.edist y p).toReal) → γ 0 = y →
      γ (g.edist y p).toReal = p →
      (∀ t ∈ Icc 0 (g.edist y p).toReal,
        g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = 1) →
      (∀ s ∈ Icc 0 (g.edist y p).toReal, ∀ t ∈ Icc 0 (g.edist y p).toReal,
        g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|) →
      g.inner y (X y) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1) ≤ -a y)
    {Φ : ℝ → M → M} (hzero : ∀ x, Φ 0 x = x)
    (horbit : ∀ x, IsMIntegralCurve (I := 𝓡 n) (fun t => Φ t x) X)
    (hadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    (hs : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ (Function.uncurry Φ))
    {x : M} (hxp : x ≠ p) : StrictMono (fun t => (g.edist p (Φ t x)).toReal) := by
  have hfix (t : ℝ) : Φ t p = p := by
    have he := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0)
      (hX.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp))
      (horbit p) (isMIntegralCurve_const hp) (hzero p)
    exact congrFun he t
  have haway (t : ℝ) : Φ t x ≠ p := by
    intro he
    have hback := hadd (-t) t x
    rw [neg_add_cancel, hzero, he, hfix] at hback
    exact hxp hback
  have hcurve : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun t => Φ t x) :=
    hs.comp (contMDiff_id.prodMk contMDiff_const)
  intro s t hst
  obtain ⟨u, hu, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr hst.le) (ha.comp hcurve.continuous).continuousOn
  have hκ : 0 < a (Φ u x) := hapos _ (haway u)
  have hinc := g.edist_increment_ge_of_inward_pairing_le D hc hst.le
    (fun v _ => hcurve v) (fun v _ => haway v) (κ := a (Φ u x)) (by
      intro v hv γ hγ hγ0 hγL hspeed hminγ
      have hvelocity : mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun t => Φ t x) v 1 = X (Φ v x) := by
        rw [(horbit x v).mfderiv]
        exact one_smul ℝ _
      rw [hvelocity]
      exact (hpair _ (haway v) γ hγ hγ0 hγL hspeed hminγ).trans
        (neg_le_neg (hmin hv)))
  have hpos := mul_pos hκ (sub_pos.mpr hst)
  linarith

end PoincareConjecture.RiemannianMetric
