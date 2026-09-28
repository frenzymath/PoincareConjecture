import PoincareConjecture.Proofs.M62.Sec19_3_CircleProductCurvature
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.Contraction
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Curvature.Bilinear
import Mathlib.Analysis.InnerProductSpace.ProdL2

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold
open scoped Manifold ContDiff Bundle BigOperators

noncomputable section

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option maxHeartbeats 800000 in

theorem circleProduct_ricci
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    {circumference : ℝ} (C : CircleGeometry circumference)
    (P : CircleProductCharts C n M)
    (G : RiemannianMetric (n + 1) P.Point) (DG : LeviCivitaData G)
    (hG : ∀ (q : P.Point) (V W : TangentSpace (𝓡 (n + 1)) q),
      G.inner q V W = g.inner q.1 (P.split q V).1 (P.split q W).1 +
        C.metricOnPoints.inner q.2 (P.split q V).2 (P.split q W).2)
    (q : P.Point) (V W : TangentSpace (𝓡 (n + 1)) q) :
    DG.ricci q V W = D.ricci q.1 (P.split q V).1 (P.split q W).1 := by
  classical
  let := P.chartedSpace
  let : RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : RiemannianBundle (TangentSpace (𝓡 1) : C.Point → Type _) :=
    ⟨C.metricOnPoints.toRiemannianMetric⟩
  let : RiemannianBundle (TangentSpace (𝓡 (n + 1)) : P.Point → Type _) :=
    ⟨G.toRiemannianMetric⟩
  let E := TangentSpace (𝓡 n) q.1
  let H := TangentSpace (𝓡 1) q.2
  let L : TangentSpace (𝓡 (n + 1)) q ≃ₗ[ℝ] WithLp 2 (E × H) :=
    (P.split q).toLinearEquiv.trans (WithLp.linearEquiv 2 ℝ (E × H)).symm
  have hL (U V : TangentSpace (𝓡 (n + 1)) q) :
      inner ℝ (L U) (L V) = inner ℝ U V := by
    change inner ℝ (WithLp.toLp 2 (P.split q U)) (WithLp.toLp 2 (P.split q V)) = _
    rw [WithLp.prod_inner_apply]
    change g.inner q.1 (P.split q U).1 (P.split q V).1 +
      C.metricOnPoints.inner q.2 (P.split q U).2 (P.split q V).2 = G.inner q U V
    exact (hG q U V).symm
  let I := L.isometryOfInner hL
  let b := g.orthonormalBasis q.1
  let c := C.metricOnPoints.orthonormalBasis q.2
  let B := (b.prod c).map I.symm
  have hb (i : Fin (Module.finrank ℝ E)) : P.split q (B (Sum.inl i)) = (b i, 0) := by
    change P.split q (I.symm ((b.prod c) (Sum.inl i))) = _
    rw [OrthonormalBasis.prod_apply]
    change P.split q ((P.split q).symm (b i, 0)) = _
    exact (P.split q).apply_symm_apply _
  have hc (i : Fin (Module.finrank ℝ H)) : P.split q (B (Sum.inr i)) = (0, c i) := by
    change P.split q (I.symm ((b.prod c) (Sum.inr i))) = _
    rw [OrthonormalBasis.prod_apply]
    change P.split q ((P.split q).symm (0, c i)) = _
    exact (P.split q).apply_symm_apply _
  have hswap (Y Z : TangentSpace (𝓡 (n + 1)) q) :
      DG.curvatureTensor q V Y W Z = DG.curvatureTensor q Y V Z W := by
    rw [M04.curvatureTensor_swap_first DG q Y V W Z,
      M04.curvatureTensor_swap_last DG q Y V W Z, neg_neg]
  have htrace : DG.ricci q V W = ∑ i, DG.curvatureTensor q V (B i) W (B i) := by
    change (∑ i, DG.curvatureTensor q V (G.orthonormalBasis q i)
      W (G.orthonormalBasis q i)) = _
    simp_rw [hswap]
    exact bilinear_sum_orthonormalBasis_eq
      (DG.curvatureTensor_bilinear_first_third q V W) (G.orthonormalBasis q) B
  rw [htrace, Fintype.sum_sum_type]
  have hbase : (∑ i, DG.curvatureTensor q V (B (Sum.inl i)) W (B (Sum.inl i))) =
      D.ricci q.1 (P.split q V).1 (P.split q W).1 := by
    unfold LeviCivitaData.ricci
    apply Finset.sum_congr rfl
    intro i _
    rw [circleProduct_curvatureTensor g D C P G DG hG, hb]
  have hcircle : (∑ i, DG.curvatureTensor q V (B (Sum.inr i)) W (B (Sum.inr i))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [circleProduct_curvatureTensor g D C P G DG hG, hc]
    change D.curvatureTensor q.1 (P.split q V).1 0 (P.split q W).1 0 = 0
    rw [M04.curvatureTensor_swap_first D q.1 0 (P.split q V).1 (P.split q W).1 0,
      M04.curvatureTensor_swap_last D q.1 0 (P.split q V).1 (P.split q W).1 0, neg_neg]
    change D.curvatureTensor_bilinear_first_third q.1 (P.split q V).1 (P.split q W).1 0 0 = 0
    simp
  rw [hbase, hcircle, add_zero]

end PoincareConjecture.M62
