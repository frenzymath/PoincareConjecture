import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.Noncollapse

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal Bundle

namespace PoincareConjecture.M30

open RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M] [SecondCountableTopology M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem volume_upper_of_precompact_ball
    (g : RiemannianMetric n M) (p : M) (hn : 1 ≤ n) {R K r : ℝ}
    (hR : 0 < R) (hK : 0 ≤ K) (hcompact : IsCompact (closure (g.ball p R)))
    (D : LeviCivitaData g)
    (hRic : ∀ x ∈ g.ball p R, ∀ v : TangentSpace (𝓡 n) x,
      -(((n : ℝ) - 1) * K) * g.inner x v v ≤ D.ricci x v v)
    (hr : 0 < r) (hrR : r < R) :
    g.volumeMeasure (g.ball p r) ≤ ENNReal.ofReal (modelVolume n K r) := by
  obtain ⟨hmono, hlim⟩ :=
    g.relativeVolumeComparison_of_precompact_ball p hn hR hK hcompact D hRic
  have hratio : g.volumeMeasure (g.ball p r) / ENNReal.ofReal (modelVolume n K r) ≤ 1 := by
    apply ge_of_tendsto hlim
    filter_upwards [Ioo_mem_nhdsGT hr] with s hs
    exact hmono ⟨hs.1, hs.2.trans hrR⟩ ⟨hr, hrR⟩ hs.2.le
  have hpos := modelVolume_pos hn hK hr
  have hvol := mul_le_mul' hratio (le_refl (ENNReal.ofReal (modelVolume n K r)))
  rw [ENNReal.div_mul_cancel (ENNReal.ofReal_pos.mpr hpos).ne'
    ENNReal.ofReal_ne_top, one_mul] at hvol
  exact hvol

theorem local_volume_bounds_of_base_volume
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (p : M)
    {a rho v K delta : ℝ} (hn : 1 ≤ n) (ha : 0 < a) (hrho : 0 < rho)
    (hv : 0 < v) (hK : 0 ≤ K)
    (hcompact : IsCompact (closure (g.ball p (3 * a + 2 * rho))))
    (hcurv : ∀ x ∈ g.ball p (3 * a + 2 * rho), D.curvatureTensorNorm x ≤ K)
    (hbase : ENNReal.ofReal v ≤ g.volumeMeasure (g.ball p rho))
    (hdelta : 0 < delta) (hdeltaL : delta ≤ a + rho) :
    0 < smallerBallVolumeBound n K (a + rho) v delta ∧
      ∀ q ∈ g.ball p a,
        ENNReal.ofReal (smallerBallVolumeBound n K (a + rho) v delta) ≤
          g.volumeMeasure (g.ball q delta) ∧
        g.volumeMeasure (g.ball q delta) ≤ ENNReal.ofReal (modelVolume n K delta) := by
  let L := a + rho
  have hL : 0 < L := add_pos ha hrho
  refine ⟨smallerBallVolumeBound_pos hn hK hL hv hdelta, ?_⟩
  intro q hq
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hqp : g.edist q p < ENNReal.ofReal a := by
    have hcomm : g.edist q p = g.edist p q := Manifold.riemannianEDist_comm
    rw [hcomm]
    exact hq
  have hbaseSub : g.ball p rho ⊆ g.ball q L := by
    intro x hx
    change g.edist q x < ENNReal.ofReal L
    calc
      g.edist q x ≤ g.edist q p + g.edist p x := Manifold.riemannianEDist_triangle
      _ < ENNReal.ofReal a + ENNReal.ofReal rho := ENNReal.add_lt_add hqp hx
      _ = ENNReal.ofReal L := (ENNReal.ofReal_add ha.le hrho.le).symm
  have houter : g.ball q (2 * L) ⊆ g.ball p (3 * a + 2 * rho) := by
    intro x hx
    change g.edist p x < ENNReal.ofReal (3 * a + 2 * rho)
    calc
      g.edist p x ≤ g.edist p q + g.edist q x := Manifold.riemannianEDist_triangle
      _ < ENNReal.ofReal a + ENNReal.ofReal (2 * L) := ENNReal.add_lt_add hq hx
      _ = ENNReal.ofReal (a + 2 * L) :=
        (ENNReal.ofReal_add ha.le (by positivity)).symm
      _ = ENNReal.ofReal (3 * a + 2 * rho) := by congr 1; dsimp [L]; ring
  have hcompactq : IsCompact (closure (g.ball q (2 * L))) :=
    hcompact.of_isClosed_subset isClosed_closure (closure_mono houter)
  have hcurvq : ∀ x ∈ g.ball q (2 * L), D.curvatureTensorNorm x ≤ K :=
    fun x hx => hcurv x (houter hx)
  have hvolq : ENNReal.ofReal v ≤ g.volumeMeasure (g.ball q L) :=
    hbase.trans (measure_mono hbaseSub)
  refine ⟨(g.smallerBall_volume_lower_bound_of_curvatureTensorNorm_le D q
    hn hK hL hv hcompactq hcurvq hvolq hdelta hdeltaL).2, ?_⟩
  apply volume_upper_of_precompact_ball g q hn (by positivity : 0 < 2 * L)
    hK hcompactq D ?_ hdelta (by dsimp [L] at *; linarith)
  exact fun x hx w => D.ricci_quadratic_lower_bound_of_curvatureTensorNorm_le
    x (hcurvq x hx) w

end PoincareConjecture.M30
