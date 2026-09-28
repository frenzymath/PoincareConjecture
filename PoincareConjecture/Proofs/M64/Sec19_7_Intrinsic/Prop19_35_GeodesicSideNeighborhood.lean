import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_FrontierReplacement
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.LocalQuadratic

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ENNReal Manifold ContDiff

namespace PoincareConjecture

private theorem connector_of_metric_segment
    (G : RiemannianMetric 2 AnnulusCoordinates) {eta : ℝ → AnnulusCoordinates}
    (hmetric : ∀ s ∈ Icc 0 1, ∀ t ∈ Icc 0 1,
      G.edist (eta s) (eta t) = ENNReal.ofReal |s - t| * G.edist (eta 0) (eta 1))
    {K : Set AnnulusCoordinates} (hconf : MapsTo eta (Icc 0 1) K)
    {p q : AnnulusCoordinates} (hp : p ∈ eta '' Icc 0 1) (hq : q ∈ eta '' Icc 0 1) :
    ∃ g : ℝ → AnnulusCoordinates, ContinuousOn g (Icc 0 1) ∧
      g 0 = p ∧ g 1 = q ∧ MapsTo g (Icc 0 1) K ∧
      m64IntrinsicCurveVariation G g 0 1 ≤ G.edist p q := by
  obtain ⟨s, hs, rfl⟩ := hp
  obtain ⟨t, ht, rfl⟩ := hq
  let f := fun x : ℝ => s + (t - s) * x
  have hf : MapsTo f (Icc 0 1) (Icc 0 1) := by
    intro x hx
    convert (convex_Icc (0 : ℝ) 1).lineMap_mem hs ht hx using 1
    simp only [f, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
    ring
  let g := fun x : ℝ => eta (f x)
  have hd (x : ℝ) (hx : x ∈ Icc 0 1) (y : ℝ) (hy : y ∈ Icc 0 1) :
      G.edist (g x) (g y) = ENNReal.ofReal |x - y| * G.edist (eta s) (eta t) := by
    dsimp only [g]
    rw [hmetric _ (hf hx) _ (hf hy), hmetric s hs t ht,
      show f x - f y = (t - s) * (x - y) by dsimp only [f]; ring,
      abs_mul, ENNReal.ofReal_mul (abs_nonneg _), abs_sub_comm t s]
    ac_rfl
  refine ⟨g, G.continuousOn_of_edist_segment (G.edist_ne_top _ _) hd,
    ?_, ?_, fun x hx => hconf (hf hx), ?_⟩
  · simp only [g, f, mul_zero, add_zero]
  · simp only [g, f, mul_one, add_sub_cancel]
  have hv := m64Intrinsic_curveVariation_le_of_edist_le G
    (C := (G.edist (eta s) (eta t)).toReal) ENNReal.toReal_nonneg (by
      intro x hx y hy
      rw [hd x hx y hy, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (G.edist_ne_top _ _), mul_comm])
  simpa only [ENNReal.ofReal_toReal (G.edist_ne_top _ _)] using hv

theorem m64Intrinsic_exists_geodesic_side_frontier_connectors
    (G : RiemannianMetric 2 AnnulusCoordinates) {alpha : ℝ → AnnulusCoordinates}
    {a b p : ℝ} (hc : ContinuousOn alpha (Icc a b))
    (hinj : InjOn alpha (Icc a b)) (hgeo : G.IsGeodesicOn alpha (Ioo a b))
    (hp : p ∈ Ioo a b) {K C : Set AnnulusCoordinates}
    (hfront : frontier K ⊆ alpha '' Icc a b ∪ C)
    (hside : MapsTo alpha (Icc a b) K) (hC : IsCompact C) (hpC : alpha p ∉ C) :
    ∃ O : Set AnnulusCoordinates, IsOpen O ∧ alpha p ∈ O ∧
      ∀ x ∈ frontier K ∩ O, ∀ y ∈ frontier K ∩ O,
        ∃ g : ℝ → AnnulusCoordinates, ContinuousOn g (Icc 0 1) ∧
          g 0 = x ∧ g 1 = y ∧ MapsTo g (Icc 0 1) K ∧
          m64IntrinsicCurveVariation G g 0 1 ≤ G.edist x y := by
  obtain ⟨delta, hdelta, hwide, _, hmetric⟩ :=
    hgeo.exists_minimizing_affine_neighborhood isOpen_Ioo hp
  let eta := fun u : ℝ => alpha (2 * delta * u + (p - delta))
  let tail := alpha '' (Icc a b \ Ioo (p - delta) (p + delta))
  have htail : IsClosed tail :=
    ((isCompact_Icc.diff isOpen_Ioo).image_of_continuousOn (hc.mono sdiff_subset)).isClosed
  have hptail : alpha p ∉ tail := by
    rintro ⟨s, hs, hsp⟩
    have hsp' : s = p := hinj hs.1 (Ioo_subset_Icc_self hp) hsp
    subst s
    exact hs.2 ⟨by linarith, by linarith⟩
  let O := (tail ∪ C)ᶜ
  have hO : IsOpen O := (htail.union hC.isClosed).isOpen_compl
  have hpO : alpha p ∈ O := by exact fun h => h.elim hptail hpC
  have hparam : MapsTo (fun u : ℝ => 2 * delta * u + (p - delta)) (Icc 0 1)
      (Icc a b) := by
    intro u hu
    apply Ioo_subset_Icc_self
    apply hwide
    constructor <;> nlinarith [hu.1, hu.2]
  have hfrontO (x : AnnulusCoordinates) (hx : x ∈ frontier K ∩ O) :
      x ∈ eta '' Icc 0 1 := by
    rcases hfront hx.1 with ⟨s, hs, rfl⟩ | hxC
    · have hsnear : s ∈ Ioo (p - delta) (p + delta) := by
        by_contra hsnear
        exact hx.2 (Or.inl ⟨s, ⟨hs, hsnear⟩, rfl⟩)
      let u := (s - (p - delta)) / (2 * delta)
      have hu : u ∈ Icc 0 1 := by
        constructor
        · exact div_nonneg (by linarith [hsnear.1]) (by positivity)
        · apply (div_le_iff₀ (by positivity : 0 < 2 * delta)).mpr
          linarith [hsnear.2]
      refine ⟨u, hu, ?_⟩
      dsimp only [eta, u]
      congr 1
      field_simp [ne_of_gt hdelta]
      ring
    · exact False.elim (hx.2 (Or.inr hxC))
  refine ⟨O, hO, hpO, ?_⟩
  intro x hx y hy
  exact connector_of_metric_segment G hmetric (fun u hu => hside (hparam hu))
    (hfrontO x hx) (hfrontO y hy)

end PoincareConjecture
