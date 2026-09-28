import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CompactGeodesicContinuation
import PoincareConjecture.Proofs.M64.Mathlib.SmoothClosedExtension
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Realization.Junction

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold

namespace PoincareConjecture

theorem m64Intrinsic_compact_geodesic_smooth_representative
    (G : RiemannianMetric 2 AnnulusCoordinates) {K : Set AnnulusCoordinates}
    (hK : IsCompact K) {a b : ℝ} (hab : a < b) {q : ℝ → AnnulusCoordinates}
    (hc : ContinuousOn q (Icc a b)) (hgeo : G.IsGeodesicOn q (Ioo a b))
    (hmap : MapsTo q (Ioo a b) K) :
    ∃ eta : ℝ → AnnulusCoordinates,
      ContDiff ℝ ∞ eta ∧ EqOn eta q (Icc a b) ∧ G.IsGeodesicOn eta (Icc a b) ∧
      HasDerivWithinAt q (deriv eta a) (Ioi a) a ∧
      HasDerivWithinAt q (deriv eta b) (Iio b) b := by
  have hca : ContinuousWithinAt q (Ici a) a := by
    have h := hc a (left_mem_Icc.mpr hab.le)
    rwa [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsGE hab] at h
  obtain ⟨epsilon, hepsilon, l, hlq, hlgeo⟩ :=
    m64Intrinsic_compact_geodesic_left_extension G hK hab hgeo hmap hca
  obtain ⟨delta, hdelta, r, hrq, _, hrgeo⟩ :=
    m64Intrinsic_compact_geodesic_right_extension G hK hab hgeo hmap
  have hrb : ContinuousAt r b :=
    (hrgeo.contMDiffAt (show b ∈ Ioo a (b + delta) from ⟨hab, by linarith⟩)).continuousAt
  have hqb : ContinuousWithinAt q (Iic b) b := by
    have h := hc b (right_mem_Icc.mpr hab.le)
    rwa [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsLE hab] at h
  have hnear : r =ᶠ[𝓝[<] b] q := by
    filter_upwards [Ioo_mem_nhdsLT hab] with t ht using hrq ht
  have hrpoint : r b = q b :=
    tendsto_nhds_unique ((hrb.tendsto.mono_left nhdsWithin_le_nhds).congr' hnear)
      (hqb.mono Iio_subset_Iic_self)
  let m := (a + b) / 2
  have ham : a < m := by dsimp only [m]; linarith
  have hmb : m < b := by dsimp only [m]; linarith
  let zeta : ℝ → AnnulusCoordinates := fun t => if t ≤ m then l t else r t
  have hleft : EqOn zeta l (Ioo (a - epsilon) b) := by
    intro t ht
    by_cases htm : t ≤ m
    · exact if_pos htm
    · have hat : a < t := ham.trans (lt_of_not_ge htm)
      exact (if_neg htm).trans ((hrq ⟨hat, ht.2⟩).trans (hlq ⟨hat.le, ht.2⟩).symm)
  have hright : EqOn zeta r (Ioo a (b + delta)) := by
    intro t ht
    by_cases htm : t ≤ m
    · have htb : t < b := htm.trans_lt hmb
      exact (if_pos htm).trans ((hlq ⟨ht.1.le, htb⟩).trans (hrq ⟨ht.1, htb⟩).symm)
    · exact if_neg htm
  have hzgeo : G.IsGeodesicOn zeta (Ioo (a - epsilon) (b + delta)) := by
    intro t ht
    by_cases htb : t < b
    · obtain ⟨p, u, v, hlocal⟩ := hlgeo t ⟨ht.1, htb⟩
      refine ⟨p, u, v, ?_⟩
      filter_upwards [hlocal, isOpen_Ioo.mem_nhds (show t ∈ Ioo (a - epsilon) b from
        ⟨ht.1, htb⟩)] with s hs hsl
      exact ⟨(hleft hsl).trans hs.1, hs.2⟩
    · have hat : a < t := hab.trans_le (le_of_not_gt htb)
      obtain ⟨p, u, v, hlocal⟩ := hrgeo t ⟨hat, ht.2⟩
      refine ⟨p, u, v, ?_⟩
      filter_upwards [hlocal, isOpen_Ioo.mem_nhds (show t ∈ Ioo a (b + delta) from
        ⟨hat, ht.2⟩)] with s hs hsr
      exact ⟨(hright hsr).trans hs.1, hs.2⟩
  have hzq : EqOn zeta q (Icc a b) := by
    intro t ht
    by_cases htm : t ≤ m
    · exact (if_pos htm).trans (hlq ⟨ht.1, htm.trans_lt hmb⟩)
    · rcases ht.2.eq_or_lt with rfl | htb
      · exact (if_neg htm).trans hrpoint
      · exact (if_neg htm).trans (hrq ⟨ham.trans (lt_of_not_ge htm), htb⟩)
  have hzsm : ContDiffOn ℝ ∞ zeta (Ioo (a - epsilon) (b + delta)) := by
    intro t ht
    exact (contMDiffAt_iff_contDiffAt.mp
      (Conjugate.Realization.contMDiffAt_of_isGeodesicOn hzgeo ht)).contDiffWithinAt
  have hsub : Icc a b ⊆ Ioo (a - epsilon) (b + delta) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  obtain ⟨eta, heta, heq⟩ :=
    m64_exists_contDiff_eq_nhds_of_isClosed isClosed_Icc isOpen_Ioo hsub hzsm
  have hclosed : EqOn eta q (Icc a b) :=
    fun t ht => (heq t ht).self_of_nhds.trans (hzq ht)
  refine ⟨eta, heta, hclosed, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨p, u, v, hlocal⟩ := hzgeo t (hsub ht)
    refine ⟨p, u, v, ?_⟩
    filter_upwards [hlocal, heq t ht] with s hs hse
    exact ⟨hse.trans hs.1, hs.2⟩
  · apply ((heta.differentiable (by simp)) a).hasDerivAt.hasDerivWithinAt.congr_of_eventuallyEq
    · filter_upwards [Ioo_mem_nhdsGT hab] with t ht using
        (hclosed (Ioo_subset_Icc_self ht)).symm
    · exact (hclosed (left_mem_Icc.mpr hab.le)).symm
  · apply ((heta.differentiable (by simp)) b).hasDerivAt.hasDerivWithinAt.congr_of_eventuallyEq
    · filter_upwards [Ioo_mem_nhdsLT hab] with t ht using
        (hclosed (Ioo_subset_Icc_self ht)).symm
    · exact (hclosed (right_mem_Icc.mpr hab.le)).symm

end PoincareConjecture
