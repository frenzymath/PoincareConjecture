import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Claim19_28.ProjectedEvolution









set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

open Set Bundle Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}



theorem m65ProjectedChart_second_hasDerivAt (P : M62.CircleProductData F circumference)
    (c : ℝ → ℝ → P.charts.Point) (hc : M62ShrinkingCurve P.flow c)
    (p : M) {t x : ℝ} (ht : t ∈ Ioo a b)
    (hx : (c x t).1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    HasDerivAt
      (deriv (fun y => (chartAt (EuclideanSpace ℝ (Fin n)) p) (c y t).1))
      (deriv (curveSpeed P.flow c t) x • m65ProjectedCoordinateJet P c p 0 t x +
        curveSpeed P.flow c t x •
          (curveSpeed P.flow c t x • m65ProjectedCoordinateJet P c p 1 t x -
            M04.shiChartChristoffel (F.connection t) (chartAt (EuclideanSpace ℝ (Fin n)) p)
              ((chartAt (EuclideanSpace ℝ (Fin n)) p) (c x t).1)
              (curveSpeed P.flow c t x • m65ProjectedCoordinateJet P c p 0 t x)
              (m65ProjectedCoordinateJet P c p 0 t x))) x := by
  have hv := ((M62.speed_contDiff P.flow c hc (Ioo_subset_Icc_self ht)).differentiable
    (by norm_num) x).hasDerivAt
  have hy := m65ProjectedCoordinateJet_hasDerivAt P c hc p ht hx 0
  have hprod := hv.smul hy
  have hbase : Continuous (fun y => (c y t).1) :=
    continuous_fst.comp (hc.spatial_regular t (Ioo_subset_Icc_self ht)).continuous
  have hcongr : HasDerivAt (deriv (fun y => (chartAt (EuclideanSpace ℝ (Fin n)) p) (c y t).1))
      (curveSpeed P.flow c t x •
        (curveSpeed P.flow c t x • m65ProjectedCoordinateJet P c p 1 t x -
          M04.shiChartChristoffel (F.connection t) (chartAt (EuclideanSpace ℝ (Fin n)) p)
            ((chartAt (EuclideanSpace ℝ (Fin n)) p) (c x t).1)
            (curveSpeed P.flow c t x • m65ProjectedCoordinateJet P c p 0 t x)
            (m65ProjectedCoordinateJet P c p 0 t x)) +
        deriv (curveSpeed P.flow c t) x • m65ProjectedCoordinateJet P c p 0 t x) x := by
    apply hprod.congr_of_eventuallyEq
    filter_upwards [hbase.continuousAt
      ((chartAt (EuclideanSpace ℝ (Fin n)) p).open_source.mem_nhds hx)] with y hy
    simpa using
      (m65ProjectedCoordinates_hasDerivAt P c hc p (Ioo_subset_Icc_self ht) hy).deriv
  simpa [add_comm] using hcongr



theorem m65ProjectedChart_evolution (P : M62.CircleProductData F circumference)
    (c : ℝ → ℝ → P.charts.Point) (hc : M62ShrinkingCurve P.flow c)
    (p : M) {t x : ℝ} (ht : t ∈ Ioo a b)
    (hx : (c x t).1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    HasDerivAt (fun r => (chartAt (EuclideanSpace ℝ (Fin n)) p) (c x r).1)
      (let q : ℝ → EuclideanSpace ℝ (Fin n) :=
        fun y => (chartAt (EuclideanSpace ℝ (Fin n)) p) (c y t).1
       (curveSpeed P.flow c t x ^ 2)⁻¹ •
          (deriv (deriv q) x +
            M04.shiChartChristoffel (F.connection t) (chartAt (EuclideanSpace ℝ (Fin n)) p)
              (q x) (deriv q x) (deriv q x)) -
         (deriv (curveSpeed P.flow c t) x / curveSpeed P.flow c t x ^ 3) • deriv q x) t := by
  let q : ℝ → EuclideanSpace ℝ (Fin n) :=
    fun y => (chartAt (EuclideanSpace ℝ (Fin n)) p) (c y t).1
  let v := curveSpeed P.flow c t
  let y := fun i => m65ProjectedCoordinateJet P c p i t
  let A := M04.shiChartChristoffel (F.connection t)
    (chartAt (EuclideanSpace ℝ (Fin n)) p) (q x)
  have hfirst : deriv q x = v x • y 0 x :=
    (m65ProjectedCoordinates_hasDerivAt P c hc p (Ioo_subset_Icc_self ht) hx).deriv
  have hsecond : deriv (deriv q) x = deriv v x • y 0 x +
      v x • (v x • y 1 x - A (v x • y 0 x) (y 0 x)) :=
    (m65ProjectedChart_second_hasDerivAt P c hc p ht hx).deriv
  have hsum : deriv (deriv q) x + A (deriv q x) (deriv q x) =
      deriv v x • y 0 x + v x ^ 2 • y 1 x := by
    rw [hfirst, hsecond]
    have hA : A (v x • y 0 x) (v x • y 0 x) =
        v x • A (v x • y 0 x) (y 0 x) := map_smul _ _ _
    rw [hA, smul_sub, smul_smul, pow_two]
    abel
  have hv : v x ≠ 0 := (M62.speed_pos P.flow c hc (Ioo_subset_Icc_self ht) x).ne'
  have hcoef : (v x ^ 2)⁻¹ * deriv v x = (deriv v x / v x ^ 3) * v x := by
    field_simp
  apply (m65ProjectedChart_time_deriv P c hc p ht hx).congr_deriv
  change y 1 x = (v x ^ 2)⁻¹ • (deriv (deriv q) x + A (deriv q x) (deriv q x)) -
    (deriv v x / v x ^ 3) • deriv q x
  rw [hsum, hfirst]
  simp only [smul_add, smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 hv), one_smul]
  rw [hcoef]
  abel

end PoincareConjecture
