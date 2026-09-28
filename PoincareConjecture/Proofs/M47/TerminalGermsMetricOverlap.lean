import PoincareConjecture.Proofs.M47.TerminalGermsOverlapLimits
import PoincareConjecture.Proofs.M47.TerminalGermsMetricRealization











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Poincare.Gluing
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M47

open ChartDistance



theorem terminalGerms_metric_pair_compatibility
    {ι : Type*} {n : ℕ}
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    (O : OverlapSystem (fun i => Piece U i)) (hs : SmoothOverlap U hU O)
    (i j : ι) (gi : CanonicalMetric U hU i) (gj : CanonicalMetric U hU j)
    (A B : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hgi : letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      letI := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
      ∀ (x : Piece U i) v w, gi.inner x v w = A x v w)
    (hgj : letI := (hU j).isOpenEmbedding_subtypeVal.singletonChartedSpace
      letI := (hU j).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
      ∀ (x : Piece U j) v w, gj.inner x v w = B x v w)
    (hcoeff : let f := coordinateRepresentative U hU (O.transition i j)
      ∀ x ∈ Subtype.val '' (O.transition i j).source, ∀ v w,
        B (f x) (fderiv ℝ f x v) (fderiv ℝ f x w) = A x v w) :
    letI : ∀ l, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U l) :=
      fun l => (hU l).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI : ∀ l, IsManifold (𝓡 n) ∞ (Piece U l) :=
      fun l => (hU l).isOpenEmbedding_subtypeVal.isManifold_singleton
    ∀ x ∈ (O.transition i j).source, ∀ v w,
      gi.inner x v w = gj.inner (O.transition i j x)
        (mfderiv (𝓡 n) (𝓡 n) (O.transition i j) x v)
        (mfderiv (𝓡 n) (𝓡 n) (O.transition i j) x w) := by
  let : ∀ l, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U l) :=
    fun l => (hU l).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ l, IsManifold (𝓡 n) ∞ (Piece U l) :=
    fun l => (hU l).isOpenEmbedding_subtypeVal.isManifold_singleton
  intro x hx v w
  have hm := hcoeff x (mem_image_of_mem Subtype.val hx) v w
  have ht := (hs i j).contMDiffAt ((O.transition i j).open_source.mem_nhds hx)
  have hd := mfderiv_eq_coordinateRepresentative U hU x (ht.mdifferentiableAt (by simp))
  simp only [hgi, hgj, hd]
  rw [coordinateRepresentative_apply] at hm
  convert hm.symm using 1
  rfl

end PoincareConjecture.M47
