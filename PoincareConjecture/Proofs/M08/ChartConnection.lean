import PoincareConjecture.Proofs.M08.ChartPullback
import PoincareConjecture.Proofs.M08.EndpointEulerCoefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

section Coefficient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local instance chartConnectionDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance chartConnectionDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance chartConnectionBilinGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance chartConnectionBilinSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

def chartChristoffelCovector (DG : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (v w : E) :
    E →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • (DG v w + DG w v - (DG.flip v).flip w)

theorem chartChristoffelCovector_apply (DG : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (v w z : E) : chartChristoffelCovector DG v w z =
      (DG v w z + DG w v z - DG z v w) / 2 := by
  simp only [chartChristoffelCovector, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.flip_apply, smul_eq_mul]
  ring

theorem chartChristoffelCovector_contDiff :
    ContDiff ℝ ∞ (fun z : (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) × (E × E) ↦
      chartChristoffelCovector z.1 z.2.1 z.2.2) := by
  have hD : ContDiff ℝ ∞
      (fun z : (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) × (E × E) ↦ z.1) := contDiff_fst
  have hDf := (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).toContinuousLinearEquiv.contDiff.comp hD
  have hDu := hDf.clm_apply contDiff_snd.fst
  have hDuf := (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.contDiff.comp hDu
  have hDuv := hDuf.clm_apply contDiff_snd.snd
  exact (contDiff_const (c := (1 / 2 : ℝ))).smul
    (((hD.clm_apply contDiff_snd.fst).clm_apply contDiff_snd.snd).add
      ((hD.clm_apply contDiff_snd.snd).clm_apply contDiff_snd.fst) |>.sub hDuv)

end Coefficient

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local instance chartConnectionModelDualGroup : NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance chartConnectionModelDualSpace : NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance chartConnectionModelBilinGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance chartConnectionModelBilinSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

def closedChartChristoffel {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (x : M) (C : Set ℝ) (z : ℝ × EuclideanSpace ℝ (Fin n))
    (v w : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  Ring.inverse (chartMetricOperator F T x z)
    ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
      (chartChristoffelCovector
        (spatialWithinFDeriv C (extChartAt (𝓡 n) x).target (chartActionMetric F T x) z) v w))

theorem chartMetricInverse_pair {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (x : M) {z : ℝ × EuclideanSpace ℝ (Fin n)}
    (hz : z.2 ∈ (extChartAt (𝓡 n) x).target)
    (η : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (w : EuclideanSpace ℝ (Fin n)) :
    chartActionMetric F T x z
        (Ring.inverse (chartMetricOperator F T x z)
          ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm η)) w = η w := by
  let v := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm η
  have hinv : chartMetricOperator F T x z (Ring.inverse (chartMetricOperator F T x z) v) = v :=
    congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) ↦ A v)
      (Ring.mul_inverse_cancel _ (chartMetricOperator_isUnit_of_target F T x hz))
  calc
    _ = inner ℝ (chartMetricOperator F T x z (Ring.inverse (chartMetricOperator F T x z) v)) w :=
      (InnerProductSpace.continuousLinearMapOfBilin_apply _ _ _).symm
    _ = η w := by rw [hinv, InnerProductSpace.toDual_symm_apply]

theorem closedChartChristoffel_pair {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (x : M) (C : Set ℝ) {z : ℝ × EuclideanSpace ℝ (Fin n)}
    (hz : z.2 ∈ (extChartAt (𝓡 n) x).target) (v w q : EuclideanSpace ℝ (Fin n)) :
    chartActionMetric F T x z (closedChartChristoffel F T x C z v w) q =
      chartChristoffelCovector
        (spatialWithinFDeriv C (extChartAt (𝓡 n) x).target (chartActionMetric F T x) z) v w q :=
  chartMetricInverse_pair F T x hz _ q

set_option maxHeartbeats 1000000 in
theorem closedChartChristoffel_contDiffOn {J C : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (x : M) (hC : UniqueDiffOn ℝ C) (htime : ∀ s ∈ C, T - s ^ 2 ∈ J) :
    ContDiffOn ℝ ∞
      (fun z : (ℝ × EuclideanSpace ℝ (Fin n)) ×
          (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ↦
        closedChartChristoffel F T x C z.1 z.2.1 z.2.2)
      ((C ×ˢ (extChartAt (𝓡 n) x).target) ×ˢ univ) := by
  let Ω := (C ×ˢ (extChartAt (𝓡 n) x).target) ×ˢ
    (univ : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
  have hfst : ContDiffOn ℝ ∞
      (Prod.fst : (ℝ × EuclideanSpace ℝ (Fin n)) ×
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →
          ℝ × EuclideanSpace ℝ (Fin n)) Ω := contDiffOn_fst
  have hmap : MapsTo Prod.fst Ω (C ×ˢ (extChartAt (𝓡 n) x).target) :=
    fun z hz ↦ hz.1
  have hB := (chartMetricInverse_closed_contDiffOn F T x htime).comp hfst hmap
  have hD := (spatialWithinFDeriv_contDiffOn hC
    (isOpen_extChartAt_target (I := 𝓡 n) x) _
    (chartActionMetric_closed_contDiffOn F T x htime)).comp hfst hmap
  have hSigma := (chartChristoffelCovector_contDiff (E := EuclideanSpace ℝ (Fin n))).comp_contDiffOn
    (hD.prodMk (contDiffOn_snd.fst.prodMk contDiffOn_snd.snd))
  exact hB.clm_apply
    ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn
      hSigma)

set_option maxHeartbeats 1000000 in
theorem closedChartChristoffel_connection {J C : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (htime : ∀ s ∈ C, T - s ^ 2 ∈ J)
    {x y : M} (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    {s : ℝ} (hs : s ∈ C) (v w : EuclideanSpace ℝ (Fin n)) :
    (F.connection (T - s ^ 2)).connection (chartFrame x w) y (chartFrame x v y) =
      chartFrame x (closedChartChristoffel F T x C (s, extChartAt (𝓡 n) x y) v w) y := by
  let g := F.metric (T - s ^ 2)
  let a := (F.connection (T - s ^ 2)).connection (chartFrame x w) y (chartFrame x v y)
  let b := chartFrame x (closedChartChristoffel F T x C (s, extChartAt (𝓡 n) x y) v w) y
  have ht : extChartAt (𝓡 n) x y ∈ (extChartAt (𝓡 n) x).target :=
    (extChartAt (𝓡 n) x).map_source (by simpa only [extChartAt_source] using hy)
  have hp (q : EuclideanSpace ℝ (Fin n)) :
      g.inner y a (chartFrame x q y) = g.inner y b (chartFrame x q y) := by
    dsimp only [a, b, g]
    rw [chartFrame_connection_koszul _ _ hy,
      ← chartActionMetric_closed_spatial_apply F T htime hy hs v w q,
      ← chartActionMetric_closed_spatial_apply F T htime hy hs w v q,
      ← chartActionMetric_closed_spatial_apply F T htime hy hs q v w,
      ← chartActionMetric_apply F T hy s, closedChartChristoffel_pair F T x C ht,
      chartChristoffelCovector_apply]
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  have hw : chartFrame x (e.continuousLinearMapAt ℝ y (a - b)) y = a - b :=
    e.symmL_continuousLinearMapAt hy _
  have heq := hp (e.continuousLinearMapAt ℝ y (a - b))
  rw [hw] at heq
  have hz : g.inner y (a - b) (a - b) = 0 := by
    calc
      _ = g.inner y a (a - b) - g.inner y b (a - b) :=
        congrArg (fun L : TangentSpace (𝓡 n) y →L[ℝ] ℝ ↦ L (a - b))
          ((g.inner y).map_sub a b)
      _ = 0 := sub_eq_zero.mpr heq
  by_contra hne
  exact (ne_of_gt (g.pos y (a - b) (sub_ne_zero.mpr hne))) hz

end PoincareConjecture.M08

