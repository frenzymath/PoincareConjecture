import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.MinimizingGeodesic
import Mathlib.Analysis.ODE.PicardLindelof











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M47

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem jointSeed_geodesic_contMDiffAt
    {g : RiemannianMetric n M} {gamma : ℝ → M} {S : Set ℝ}
    (hgamma : g.IsGeodesicOn gamma S) {t : ℝ} (ht : t ∈ S) :
    ContMDiffAt (𝓘(ℝ, ℝ)) (𝓡 n) ∞ gamma t := by
  obtain ⟨p, q, w, hlocal⟩ := hgamma t ht
  obtain ⟨a, b, _htab, hnbhd, hab⟩ := exists_Icc_mem_subset_of_mem_nhds hlocal
  let B := g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
  let U := (extChartAt (𝓡 n) p).target ×ˢ (univ : Set (EuclideanSpace ℝ (Fin n)))
  have hfield : ContDiffOn ℝ ∞
      (fun z : ℝ × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =>
        coordinateGeodesicField B z.2) (Icc a b ×ˢ U) := by
    intro z hz
    have hzsrc : z.2.1 ∈ (extChartAt (𝓡 n) p).target := hz.2.1
    have hB : ContDiffAt ℝ ∞ B z.2.1 :=
      (g.contDiffOn_chartCoefficients p z.2.1 hzsrc).contDiffAt
        ((isOpen_extChartAt_target (I := 𝓡 n) p).mem_nhds hzsrc)
    exact ((contDiffAt_coordinateGeodesicField hB
      (g.isInvertible_chartCoefficients p hzsrc)).comp z contDiffAt_snd).contDiffWithinAt
  have hphase (s : ℝ) (hs : s ∈ Icc a b) :
      HasDerivWithinAt (fun s => (q s, w s))
        (coordinateGeodesicField B (q s, w s)) (Icc a b) s := by
    exact ((hab hs).2.2.1.prodMk (hab hs).2.2.2).hasDerivWithinAt
  have hmem : MapsTo (fun s => (q s, w s)) (Icc a b) U :=
    fun s hs => ⟨(hab hs).2.1, mem_univ _⟩
  have hphaseSmooth := ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt (n := ⊤)
    (f := fun _ z => coordinateGeodesicField B z) hfield hphase hmem
  have hcurve : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞
      (fun s => (extChartAt (𝓡 n) p).symm (q s)) (Icc a b) :=
    (contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := ∞) p).comp
      (contMDiffOn_iff_contDiffOn.mpr hphaseSmooth.fst) (fun s hs => (hab hs).2.1)
  exact (hcurve.contMDiffAt hnbhd).congr_of_eventuallyEq
    (hlocal.mono fun s hs => hs.1)



theorem jointSeed_geodesic_contMDiffOn
    {g : RiemannianMetric n M} {gamma : ℝ → M} {S : Set ℝ}
    (hgamma : g.IsGeodesicOn gamma S) :
    ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ gamma S :=
  fun _ ht => (jointSeed_geodesic_contMDiffAt hgamma ht).contMDiffWithinAt

end PoincareConjecture.M47
