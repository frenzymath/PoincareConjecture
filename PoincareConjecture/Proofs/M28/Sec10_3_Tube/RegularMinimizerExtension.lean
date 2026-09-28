import PoincareConjecture.Proofs.M28.Mathlib.PathLengthBallAnchors
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicMinimizerSubsegments
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceEdgeMinimizerOverlap
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.OpenRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Calibration













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]





theorem exists_radial_gain_of_regular_regional_minimizer
    (g : RiemannianMetric 3 M) (T : TopologicalSpace.Opens M)
    (V : TopologicalSpace.Opens T) (z : T) (x : V)
    {R : Set M} {γ : ℝ → M} {c v delta e L : ℝ}
    (hTR : (T : Set M) ⊆ R)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc (0 : ℝ) 1))
    (hγR : MapsTo γ (Icc (0 : ℝ) 1) R)
    (hfinite : g.pathELength γ 0 1 ≠ ⊤)
    (hmin : g.pathELength γ 0 1 = intrinsicEDist g R (γ 0) (γ 1))
    (hzero : γ 0 ∉ (T : Set M)) (hone : γ 1 ∉ (T : Set M))
    (hc : c ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1)
    (hbase : γ c = (z : M)) (hvT : γ v ∈ (T : Set M))
    (hbasepath : MapsTo γ (Icc (min c v) (max c v)) (T : Set M))
    (hregular : x ∈ regularPoints (intrinsicOpenMetric (intrinsicOpenMetric g T) V) delta)
    (he : 0 ≤ e) (hL : 0 < L) (hbudget : e + L < delta)
    (hconnector : (intrinsicOpenMetric g T).edist (x : T) ⟨γ v, hvT⟩ ≤
      ENNReal.ofReal e) :
    ∃ y : V,
      (intrinsicOpenMetric g T).edist z (x : T) + ENNReal.ofReal L ≤
        (intrinsicOpenMetric g T).edist z (y : T) + ENNReal.ofReal e := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : T → Type _) :=
    ⟨(intrinsicOpenMetric g T).toRiemannianMetric⟩
  let q : T := ⟨γ v, hvT⟩
  have himage := nested_intrinsicOpenMetric_ball_image_of_regular g T V x hregular
  have hcapture : g.ball ((x : T) : M) delta ⊆ (T : Set M) := by
    intro p hp
    rw [← himage] at hp
    obtain ⟨y, _, rfl⟩ := hp
    exact (y : T).property
  have hstart : g.edist ((x : T) : M) (γ v) ≤ ENNReal.ofReal e := by
    have hle := RiemannianMetric.edist_le_intrinsicEDist g (T : Set M)
      ((x : T) : M) (γ v)
    rw [← intrinsicOpenMetric_edist g T (x : T) q] at hle
    exact hle.trans hconnector
  have hsubmin (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
      (hpath : MapsTo γ (Icc a b) (T : Set M)) :
      g.pathELength γ a b = intrinsicEDist g (T : Set M) (γ a) (γ b) := by
    have hregional := pathELength_eq_intrinsicEDist_subsegment g ha hab hb
      hγ hγR hfinite hmin
    apply le_antisymm
    · rw [hregional]
      exact intrinsicEDist_mono_of_subset (g := g) hTR
    · exact intrinsicEDist_le_pathELength g hab
        (hγ.mono (Icc_subset_Icc ha hb)) hpath
  have hcomm (p q : T) : (intrinsicOpenMetric g T).edist p q =
      (intrinsicOpenMetric g T).edist q p := Manifold.riemannianEDist_comm
  have htriangle : (intrinsicOpenMetric g T).edist z (x : T) ≤
      (intrinsicOpenMetric g T).edist z q + ENNReal.ofReal e := by
    calc
      _ ≤ (intrinsicOpenMetric g T).edist z q +
          (intrinsicOpenMetric g T).edist q (x : T) :=
        Manifold.riemannianEDist_triangle
      _ ≤ _ := add_le_add (le_refl _) (by
        simpa only [hcomm q (x : T), q] using hconnector)
  have hgain (y : V)
      (hradial : (intrinsicOpenMetric g T).edist z q + ENNReal.ofReal L =
        (intrinsicOpenMetric g T).edist z (y : T)) :
      (intrinsicOpenMetric g T).edist z (x : T) + ENNReal.ofReal L ≤
        (intrinsicOpenMetric g T).edist z (y : T) + ENNReal.ofReal e := by
    calc
      _ ≤ ((intrinsicOpenMetric g T).edist z q + ENNReal.ofReal e) +
          ENNReal.ofReal L := add_le_add htriangle (le_refl _)
      _ = ((intrinsicOpenMetric g T).edist z q + ENNReal.ofReal L) +
          ENNReal.ofReal e := by ac_rfl
      _ = _ := by rw [hradial]
  by_cases hcv : c ≤ v
  · have hv1 : v < 1 := lt_of_le_of_ne hv.2 (by
      intro h
      exact hone (h ▸ hvT))
    obtain ⟨b, hb, hlength, hball⟩ := exists_pathELength_right_anchor_in_ball g hv1
      (hγ.mono (Icc_subset_Icc hv.1 le_rfl)) he hL hbudget hstart hone hcapture
    have hyball := hball (right_mem_Icc.mpr hb.1.le)
    rw [← himage] at hyball
    obtain ⟨y, _, hy⟩ := hyball
    change ((y : T) : M) = γ b at hy
    have hprefix : MapsTo γ (Icc c v) (T : Set M) := by
      simpa only [min_eq_left hcv, max_eq_right hcv] using hbasepath
    have hwhole : MapsTo γ (Icc c b) (T : Set M) := by
      intro t ht
      by_cases htv : t ≤ v
      · exact hprefix ⟨ht.1, htv⟩
      · exact hcapture (hball ⟨(lt_of_not_ge htv).le, ht.2⟩)
    have hdistv : (intrinsicOpenMetric g T).edist z q = g.pathELength γ c v := by
      rw [intrinsicOpenMetric_edist]
      change intrinsicEDist g (T : Set M) (z : M) (γ v) = _
      rw [← hbase]
      exact (hsubmin c v hc.1 hcv hv.2 hprefix).symm
    have hdistb : (intrinsicOpenMetric g T).edist z (y : T) =
        g.pathELength γ c b := by
      rw [intrinsicOpenMetric_edist]
      rw [← hbase, hy]
      exact (hsubmin c b hc.1 (hcv.trans hb.1.le) hb.2.le hwhole).symm
    refine ⟨y, hgain y ?_⟩
    rw [hdistv, hdistb, ← hlength]
    exact Manifold.pathELength_add hcv hb.1.le
  · have hvc : v ≤ c := (lt_of_not_ge hcv).le
    have hv0 : 0 < v := lt_of_le_of_ne hv.1 (by
      intro h
      exact hzero (h ▸ hvT))
    obtain ⟨a, ha, hlength, hball⟩ := exists_pathELength_left_anchor_in_ball g hv0
      (hγ.mono (Icc_subset_Icc le_rfl hv.2)) he hL hbudget hstart hzero hcapture
    have hyball := hball (left_mem_Icc.mpr ha.2.le)
    rw [← himage] at hyball
    obtain ⟨y, _, hy⟩ := hyball
    change ((y : T) : M) = γ a at hy
    have hprefix : MapsTo γ (Icc v c) (T : Set M) := by
      simpa only [min_eq_right hvc, max_eq_left hvc] using hbasepath
    have hwhole : MapsTo γ (Icc a c) (T : Set M) := by
      intro t ht
      by_cases hvt : v ≤ t
      · exact hprefix ⟨hvt, ht.2⟩
      · exact hcapture (hball ⟨ht.1, (lt_of_not_ge hvt).le⟩)
    have hdistv : (intrinsicOpenMetric g T).edist z q = g.pathELength γ v c := by
      rw [hcomm z q, intrinsicOpenMetric_edist]
      change intrinsicEDist g (T : Set M) (γ v) (z : M) = _
      rw [← hbase]
      exact (hsubmin v c hv.1 hvc hc.2 hprefix).symm
    have hdista : (intrinsicOpenMetric g T).edist z (y : T) =
        g.pathELength γ a c := by
      rw [hcomm z (y : T), intrinsicOpenMetric_edist]
      rw [← hbase, hy]
      exact (hsubmin a c ha.1.le (ha.2.le.trans hvc) hc.2 hwhole).symm
    refine ⟨y, hgain y ?_⟩
    rw [hdistv, hdista, ← hlength, add_comm]
    exact Manifold.pathELength_add ha.2.le hvc

end PoincareConjecture.M28
