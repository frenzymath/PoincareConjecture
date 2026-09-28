import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.InitialData
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Uniqueness










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

omit [T2Space M] in
private theorem geodesic_congr_nhds
    {γ η : ℝ → M} {s : Set ℝ} {t : ℝ}
    (hγ : g.IsGeodesicOn γ s) (ht : t ∈ s) (heq : η =ᶠ[𝓝 t] γ) :
    ∃ p : M, ∃ q w : ℝ → EuclideanSpace ℝ (Fin n),
      ∀ᶠ u in 𝓝 t,
        η u = (extChartAt (𝓡 n) p).symm (q u) ∧
        q u ∈ (extChartAt (𝓡 n) p).target ∧ HasDerivAt q (w u) u ∧
        HasDerivAt w
          (-coordinateChristoffel (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm)
            (q u) (w u) (w u)) u := by
  obtain ⟨p, q, w, h⟩ := hγ t ht
  refine ⟨p, q, w, ?_⟩
  filter_upwards [h, heq] with u hu hueq
  exact ⟨hueq.trans hu.1, hu.2⟩



theorem exists_geodesic_through_one_of_precompact_ball
    (g : RiemannianMetric n M) (p : M) {R : ℝ} (hR : 0 < R)
    (hcompact : IsCompact (closure (g.ball p R)))
    (v : EuclideanSpace ℝ (Fin n))
    (hv : Real.sqrt (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
      (extChartAt (𝓡 n) p p) v v) < R) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → M,
      g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) ∧ γ 0 = p ∧
      HasDerivAt (fun t => extChartAt (𝓡 n) p (γ t)) v 0 ∧
      g.edist p (γ 1) ≤ ENNReal.ofReal
        (Real.sqrt (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
          (extChartAt (𝓡 n) p p) v v)) := by
  classical
  obtain ⟨δ, hδ, hδ1, γ₀, hγ₀, hγ₀p, hγ₀v⟩ := g.exists_geodesic_initial_data p v
  let T : Set ℝ := {b | δ ≤ b ∧ ∃ γ : ℝ → M,
    g.IsGeodesicOn γ (Ioo (-δ) b) ∧ γ =ᶠ[𝓝 0] γ₀}
  have hδT : δ ∈ T := ⟨le_rfl, γ₀, hγ₀, EventuallyEq.rfl⟩
  have hTex : ∃ b ∈ T, 1 < b := by
    by_contra hnot
    have hupper : ∀ b ∈ T, b ≤ 1 := by
      intro b hb
      by_contra h
      exact hnot ⟨b, hb, lt_of_not_ge h⟩
    have hbounded : BddAbove T := ⟨1, hupper⟩
    let b := sSup T
    have hδb : δ ≤ b := le_csSup hbounded hδT
    have hb1 : b ≤ 1 := csSup_le ⟨δ, hδT⟩ hupper
    choose f hf using fun t (ht : t ∈ T) => ht.2
    have hcompat (r : ℝ) (hr : r ∈ T) (s : ℝ) (hs : s ∈ T) :
        EqOn (f r hr) (f s hs) (Ioo (-δ) (min r s)) := by
      have hzero : (0 : ℝ) ∈ Ioo (-δ) (min r s) :=
        ⟨by linarith, lt_min (hδ.trans_le hr.1) (hδ.trans_le hs.1)⟩
      exact (show g.IsGeodesicOn (f r hr) (Ioo (-δ) (min r s)) from
        fun t ht => (hf r hr).1 t ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩)
        |>.eqOn_of_eventuallyEq
          (fun t ht => (hf s hs).1 t ⟨ht.1, ht.2.trans_le (min_le_right _ _)⟩)
          isOpen_Ioo (convex_Ioo _ _).isPreconnected hzero
          ((hf r hr).2.trans (hf s hs).2.symm)
    let Γ : ℝ → M := fun t =>
      if ht : ∃ r ∈ T, t < r then
        f ht.choose ht.choose_spec.1 t
      else γ₀ t
    have hΓeq (r : ℝ) (hr : r ∈ T) : EqOn Γ (f r hr) (Ioo (-δ) r) := by
      intro t ht
      have hex : ∃ s ∈ T, t < s := ⟨r, hr, ht.2⟩
      change (if h : ∃ s ∈ T, t < s then f h.choose h.choose_spec.1 t else γ₀ t) = _
      rw [dif_pos hex]
      exact hcompat hex.choose hex.choose_spec.1 r hr
        ⟨ht.1, lt_min hex.choose_spec.2 ht.2⟩
    have hΓgerm (r : ℝ) (hr : r ∈ T) {t : ℝ} (ht : t ∈ Ioo (-δ) r) :
        Γ =ᶠ[𝓝 t] f r hr := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
      exact hΓeq r hr hu
    have hΓ : g.IsGeodesicOn Γ (Ioo (-δ) b) := by
      intro t ht
      obtain ⟨r, hr, htr⟩ := exists_lt_of_lt_csSup ⟨δ, hδT⟩ ht.2
      exact geodesic_congr_nhds (hf r hr).1 ⟨ht.1, htr⟩
        (hΓgerm r hr ⟨ht.1, htr⟩)
    have hzero : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
    have hgerm : Γ =ᶠ[𝓝 0] γ₀ := (hΓgerm δ hδT hzero).trans (hf δ hδT).2
    have hΓp : Γ 0 = p := hgerm.self_of_nhds.trans hγ₀p
    have hΓv : HasDerivAt (fun t => extChartAt (𝓡 n) p (Γ t)) v 0 :=
      hγ₀v.congr_of_eventuallyEq (hgerm.mono fun _ h => congrArg _ h)
    have hΓS : MapsTo Γ (Ioo (-δ) b) (closure (g.ball p R)) := by
      intro t ht
      apply subset_closure
      have hdist := hΓ.edist_le_initial_speed ⟨by linarith, hδ.trans_le hδb⟩ hΓp hΓv ht
      have ht1 : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2.le.trans hb1⟩
      have htE : ENNReal.ofReal |t| ≤ 1 := by
        simpa using ENNReal.ofReal_le_ofReal ht1
      change g.edist p (Γ t) < ENNReal.ofReal R
      apply lt_of_le_of_lt (hdist.trans (mul_le_of_le_one_right' htE))
      exact (ENNReal.ofReal_lt_ofReal_iff hR).mpr hv
    obtain ⟨ε, hε, η, hηeq, hη⟩ :=
      g.exists_geodesic_continuation_of_compact_confinement
        (by linarith : -δ < b) hΓ hcompact hΓS
    have hηgerm : η =ᶠ[𝓝 0] γ₀ := by
      apply EventuallyEq.trans _ hgerm
      filter_upwards [isOpen_Ioo.mem_nhds
        (show (0 : ℝ) ∈ Ioo (-δ) b from ⟨by linarith, hδ.trans_le hδb⟩)] with t ht
      exact hηeq ht
    have hnew : b + ε ∈ T := ⟨by linarith, η, hη, hηgerm⟩
    have hle := le_csSup hbounded hnew
    change b + ε ≤ b at hle
    linarith
  obtain ⟨b, hb, hb1⟩ := hTex
  obtain ⟨γ, hγ, hgerm⟩ := hb.2
  let ε := min δ ((b - 1) / 2)
  have hε : 0 < ε := lt_min hδ (by linarith)
  have hsub : Ioo (-ε) (1 + ε) ⊆ Ioo (-δ) b := by
    intro t ht
    have heδ : ε ≤ δ := min_le_left _ _
    have heb : ε ≤ (b - 1) / 2 := min_le_right _ _
    constructor <;> linarith [ht.1, ht.2]
  have hp : γ 0 = p := hgerm.self_of_nhds.trans hγ₀p
  have hd : HasDerivAt (fun t => extChartAt (𝓡 n) p (γ t)) v 0 :=
    hγ₀v.congr_of_eventuallyEq (hgerm.mono fun _ h => congrArg _ h)
  refine ⟨ε, hε, γ, (fun t ht => hγ t (hsub ht)), hp, hd, ?_⟩
  simpa using hγ.edist_le_initial_speed (by constructor <;> linarith) hp hd
    (t := 1) (by constructor <;> linarith)

end PoincareConjecture.RiemannianMetric
