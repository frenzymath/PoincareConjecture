import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ProductRicciTraceBound
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusClosedConformality












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem curvature_four_norm_bound
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x : M)
    (u v : TangentSpace (𝓡 n) x) :
    |D.curvatureTensor x u v u v| ≤ D.curvatureTensorNorm x *
      g.inner x u u * g.inner x v v := by
  let A : MultilinearMap ℝ (fun _ : Fin 4 => TangentSpace (𝓡 n) x) ℝ :=
    { toFun := fun w => D.curvatureTensor x (w 0) (w 1) (w 2) (w 3)
      map_update_add' := by
        classical
        intro _ w i a b
        fin_cases i
        · simpa [Function.update, Fin.ext_iff] using
            D.curvatureTensor_add_first x a b (w 1) (w 2) (w 3)
        · simpa [Function.update, Fin.ext_iff] using
            D.curvatureTensor_add_second x (w 0) a b (w 2) (w 3)
        · simpa [Function.update, Fin.ext_iff] using
            D.curvatureTensor_add_third x (w 0) (w 1) a (w 3) b
        · simpa [Function.update, Fin.ext_iff] using
            D.curvatureTensor_add_last x (w 0) (w 1) (w 2) a b
      map_update_smul' := by
        classical
        intro _ w i c a
        fin_cases i
        · simpa [Function.update, Fin.ext_iff] using
            D.curvatureTensor_smul_first x c a (w 1) (w 2) (w 3)
        · simpa [Function.update, Fin.ext_iff] using
            D.curvatureTensor_smul_second x c (w 0) a (w 2) (w 3)
        · simpa [Function.update, Fin.ext_iff] using
            D.curvatureTensor_smul_third x c (w 0) (w 1) a (w 3)
        · simpa [Function.update, Fin.ext_iff] using
            D.curvatureTensor_smul_last x c (w 0) (w 1) (w 2) a }
  have h := D.abs_curvatureTensor_le_of_multilinear x A (fun _ => rfl) u v u v
  have hnorm (w : TangentSpace (𝓡 n) x) : g.tangentNorm x w ^ 2 = g.inner x w w :=
    Real.sq_sqrt ((g.toRiemannianMetric.toCore x).re_inner_nonneg w)
  calc
    _ ≤ D.curvatureTensorNorm x * g.tangentNorm x u * g.tangentNorm x v *
        g.tangentNorm x u * g.tangentNorm x v := h
    _ = D.curvatureTensorNorm x * g.tangentNorm x u ^ 2 * g.tangentNorm x v ^ 2 := by ring
    _ = _ := by rw [hnorm, hnorm]

variable {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}





theorem m64CircleProduct_orthogonal_sectional_abs_le
    (P : M62.CircleProductData F circumference) (t : ℝ) {K : ℝ} (hK : 0 ≤ K)
    (q : P.charts.Point) (hcurv : (F.connection t).curvatureTensorNorm q.1 ≤ K)
    (u v : TangentSpace (𝓡 (n + 1)) q)
    (horth : (P.flow.metric t).inner q u v = 0) :
    |(P.flow.connection t).sectionalCurvature q u v| ≤ K := by
  let g := F.metric t
  let G := P.flow.metric t
  let ub := (P.charts.split q u).1
  let vb := (P.charts.split q v).1
  have hu0 : 0 ≤ g.inner q.1 ub ub :=
    (g.toRiemannianMetric.toCore q.1).re_inner_nonneg ub
  have hv0 : 0 ≤ g.inner q.1 vb vb :=
    (g.toRiemannianMetric.toCore q.1).re_inner_nonneg vb
  have huG : 0 ≤ G.inner q u u := (G.toRiemannianMetric.toCore q).re_inner_nonneg u
  have hvG : 0 ≤ G.inner q v v := (G.toRiemannianMetric.toCore q).re_inner_nonneg v
  have hproj (w : TangentSpace (𝓡 (n + 1)) q) :
      g.inner q.1 (P.charts.split q w).1 (P.charts.split q w).1 ≤ G.inner q w w := by
    rw [P.metric_eq]
    exact le_add_of_nonneg_right
      ((P.circle.metricOnPoints.toRiemannianMetric.toCore q.2).re_inner_nonneg _)
  have hnum : |(P.flow.connection t).curvatureTensor q u v u v| ≤
      K * G.inner q u u * G.inner q v v := by
    rw [M62.circleProduct_curvatureTensor (F.metric t) (F.connection t) P.circle P.charts
      (P.flow.metric t) (P.flow.connection t) (P.metric_eq t)]
    calc
      _ ≤ (F.connection t).curvatureTensorNorm q.1 * g.inner q.1 ub ub *
          g.inner q.1 vb vb := curvature_four_norm_bound (F.connection t) q.1 ub vb
      _ ≤ K * g.inner q.1 ub ub * g.inner q.1 vb vb :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcurv hu0) hv0
      _ ≤ K * G.inner q u u * G.inner q v v := by
        have hm := mul_le_mul (hproj u) (hproj v) hv0 huG
        nlinarith [mul_le_mul_of_nonneg_left hm hK]
  have hden : 0 ≤ G.inner q u u * G.inner q v v := mul_nonneg huG hvG
  by_cases hz : G.inner q u u * G.inner q v v = 0
  · rw [(P.flow.connection t).sectionalCurvature_eq_zero_of_gramDet_eq_zero q u v
      (by simpa only [horth, zero_pow (by decide : 2 ≠ 0), sub_zero] using hz), abs_zero]
    exact hK
  have hpos : 0 < G.inner q u u * G.inner q v v := lt_of_le_of_ne hden (Ne.symm hz)
  unfold LeviCivitaData.sectionalCurvature
  rw [horth, zero_pow (by decide : 2 ≠ 0), sub_zero, abs_div, abs_of_pos hpos]
  exact (div_le_iff₀ hpos).mpr (hnum.trans_eq (by ring))





theorem m64CircleProduct_conformal_annulus_sectional_le
    (P : M62.CircleProductData F circumference) (t : ℝ)
    {c0 c1 : ℝ → P.charts.Point} (A : M64Annulus (P.flow.metric t) c0 c1)
    {O : Set LoopPlane} (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    (hA : ContMDiffOn (𝓡 2) (𝓡 (n + 1)) ∞ A.map O)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      m60AreaGram (P.flow.metric t) A.map p 0 0 = m60AreaGram (P.flow.metric t) A.map p 1 1 ∧
        m60AreaGram (P.flow.metric t) A.map p 0 1 = 0)
    {K : ℝ} (hK : 0 ≤ K)
    (hcurv : ∀ x : M, (F.connection t).curvatureTensorNorm x ≤ K) :
    ∀ p ∈ m64AnnulusInterior, (P.flow.connection t).sectionalCurvature (A.map p)
      (mfderiv (𝓡 2) (𝓡 (n + 1)) A.map p (EuclideanSpace.single (0 : Fin 2) 1))
      (mfderiv (𝓡 2) (𝓡 (n + 1)) A.map p (EuclideanSpace.single (1 : Fin 2) 1)) ≤ K := by
  intro p hp
  have hsub : m64AnnulusInterior ⊆ m64AnnulusDomain := by
    rw [← m64AnnulusInterior_closure]
    exact subset_closure
  have hc := (m64Annulus_conformal_on_domain_of_ae A hO hdom hA hconformal p (hsub hp)).2
  have ho : (P.flow.metric t).inner (A.map p)
      (mfderiv (𝓡 2) (𝓡 (n + 1)) A.map p (EuclideanSpace.single (0 : Fin 2) 1))
      (mfderiv (𝓡 2) (𝓡 (n + 1)) A.map p (EuclideanSpace.single (1 : Fin 2) 1)) = 0 := by
    simpa only [m60AreaGram, EuclideanSpace.basisFun_apply] using hc
  exact (le_abs_self _).trans
    (m64CircleProduct_orthogonal_sectional_abs_le P t hK (A.map p) (hcurv (A.map p).1) _ _ ho)

end PoincareConjecture
