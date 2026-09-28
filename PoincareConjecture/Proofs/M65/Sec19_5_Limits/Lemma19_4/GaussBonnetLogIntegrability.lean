import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetAmbientBound











set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M65Gauss

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

private theorem abs_metric_pair_le_half (x u v : EuclideanSpace ℝ (Fin n)) :
    |g.euclideanCoefficients x u v| ≤
      (g.euclideanCoefficients x u u + g.euclideanCoefficients x v v) / 2 := by
  have hpos (w : EuclideanSpace ℝ (Fin n)) : 0 ≤ g.euclideanCoefficients x w w := by
    by_cases hw : w = 0
    · simp [hw]
    · exact (g.pos x w hw).le
  have hp := hpos (u + v)
  have hm := hpos (u - v)
  simp only [map_add, add_apply, map_sub, sub_apply] at hp hm
  have hs : g.euclideanCoefficients x v u = g.euclideanCoefficients x u v := g.symm x v u
  rw [hs] at hp hm
  exact abs_le.mpr ⟨by linarith, by linarith⟩






theorem logarithmicDensity_integrableOn (D : LeviCivitaData g)
    {F : LoopPlane → EuclideanSpace ℝ (Fin n)} {K U : Set LoopPlane}
    (hK : IsCompact K) (hU : IsOpen U) (hF : ContinuousOn F K)
    (hFs : ContDiffOn ℝ ∞ F U) {lam : LoopPlane → ℝ}
    (hlam : ContinuousOn lam K) (hlams : ContDiffOn ℝ ∞ lam U)
    (hconf : ∀ x ∈ U, 0 < lam x ∧
      m60AreaGram g F x = lam x • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (hN : ∀ i j : Fin 2, IntegrableOn (fun x =>
      let B := normalHessian D F x (EuclideanSpace.basisFun (Fin 2) ℝ i)
        (EuclideanSpace.basisFun (Fin 2) ℝ j)
      g.inner (F x) B B / lam x) (K ∩ U) volume) :
    IntegrableOn (fun x => -(∑ i : Fin 2, fderiv ℝ (fun y =>
      fderiv ℝ (fun z => Real.log (lam z)) y (EuclideanSpace.basisFun (Fin 2) ℝ i))
        x (EuclideanSpace.basisFun (Fin 2) ℝ i)) / 2) (K ∩ U) volume := by
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  let N (i j : Fin 2) (x : LoopPlane) := normalHessian D F x (e i) (e j)
  let q (i j : Fin 2) (x : LoopPlane) :=
    g.euclideanCoefficients (F x) (N i j x) (N i j x) / lam x
  let G := fun x => -(∑ i : Fin 2, fderiv ℝ (fun y =>
    fderiv ℝ (fun z => Real.log (lam z)) y (e i)) x (e i)) / 2
  have hmetricC : ContinuousOn (fun x => g.euclideanCoefficients (F x)) K :=
    (contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients).continuous.comp_continuousOn hF
  obtain ⟨a, C, ha, _hC, hmetric⟩ := Proofs.M03.exists_pos_uniform_bilinear_bounds hK hmetricC
    (fun x _ v hv => g.pos (F x) v hv)
  have hRC : ContinuousOn (fun x => curvatureCoefficientBound D (F x)) K :=
    (curvatureCoefficientBound_continuous D).comp_continuousOn hF
  obtain ⟨CR, hCR⟩ := hK.exists_bound_of_continuousOn hRC
  let B := max CR 0 / a ^ 2
  have hmajor : IntegrableOn (fun x => B * lam x + (q 0 0 x + q 1 1 x) / 2 + q 0 1 x)
      (K ∩ U) volume :=
    (((hlam.const_mul B).integrableOn_compact hK).mono_set inter_subset_left).add
      (((hN 0 0).add (hN 1 1)).div_const 2) |>.add (hN 0 1)
  have hlog : ContDiffOn ℝ ∞ (fun z => Real.log (lam z)) U :=
    hlams.log (fun x hx => (hconf x hx).1.ne')
  have hpartial (i : Fin 2) :
      ContDiffOn ℝ ∞ (fun y => fderiv ℝ (fun z => Real.log (lam z)) y (e i)) U :=
    (hlog.fderiv_of_isOpen (m := ∞) hU (by simp)).clm_apply contDiffOn_const
  have hsecond (i : Fin 2) : ContinuousOn (fun x => fderiv ℝ (fun y =>
      fderiv ℝ (fun z => Real.log (lam z)) y (e i)) x (e i)) U :=
    ((hpartial i).fderiv_of_isOpen (m := 0) hU (by simp)).continuousOn.clm_apply continuousOn_const
  have hGC : ContinuousOn G U :=
    ((continuousOn_finsetSum Finset.univ (fun i _ => hsecond i)).neg).div_const 2
  have hKU : MeasurableSet (K ∩ U) := hK.measurableSet.inter hU.measurableSet
  apply hmajor.mono' ((hGC.mono inter_subset_right).aestronglyMeasurable hKU)
  filter_upwards [ae_restrict_mem hKU] with x hx
  let u := fderiv ℝ F x (e 0)
  let v := fderiv ℝ F x (e 1)
  have hlampos := (hconf x hx.2).1
  have hcol (i : Fin 2) : ‖fderiv ℝ F x (e i)‖ ^ 2 ≤ lam x / a := by
    have he : g.euclideanCoefficients (F x) (fderiv ℝ F x (e i))
        (fderiv ℝ F x (e i)) = lam x := by
      have hh := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A i i) (hconf x hx.2).2
      simpa +instances only [m60AreaGram, mfderiv_eq_fderiv, Matrix.smul_apply,
        Matrix.one_apply_eq, smul_eq_mul, mul_one] using! hh
    apply (le_div_iff₀ ha).mpr
    simpa only [he, mul_comm] using (hmetric x hx.1 (fderiv ℝ F x (e i))).1
  have hcurvBound : |D.curvatureTensor (F x) u v u v| / lam x ≤ B * lam x := by
    have hb0 : 0 ≤ max CR 0 := le_max_right _ _
    have hcurv := abs_curvatureTensor_le_coefficient D (F x) u v
    have hcoef : curvatureCoefficientBound D (F x) ≤ max CR 0 :=
      (le_abs_self _).trans ((hCR x hx.1).trans (le_max_left _ _))
    have hcol0 : ‖u‖ ^ 2 ≤ lam x / a := hcol 0
    have hcol1 : ‖v‖ ^ 2 ≤ lam x / a := hcol 1
    have hnorm : |D.curvatureTensor (F x) u v u v| ≤
        max CR 0 * (lam x / a) * (lam x / a) :=
      hcurv.trans ((mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖u‖)) (sq_nonneg ‖v‖)).trans
          (mul_le_mul (mul_le_mul_of_nonneg_left hcol0 hb0) hcol1
            (sq_nonneg ‖v‖) (mul_nonneg hb0 (div_nonneg hlampos.le ha.le))))
    calc
      _ ≤ (max CR 0 * (lam x / a) * (lam x / a)) / lam x :=
        div_le_div_of_nonneg_right hnorm hlampos.le
      _ = _ := by dsimp only [B]; field_simp
  have hpos (w : EuclideanSpace ℝ (Fin n)) : 0 ≤ g.euclideanCoefficients (F x) w w :=
    (mul_nonneg ha.le (sq_nonneg ‖w‖)).trans (hmetric x hx.1 w).1
  have hpair : |g.euclideanCoefficients (F x) (N 0 0 x) (N 1 1 x)| / lam x ≤
      (q 0 0 x + q 1 1 x) / 2 := by
    calc
      _ ≤ ((g.euclideanCoefficients (F x) (N 0 0 x) (N 0 0 x) +
          g.euclideanCoefficients (F x) (N 1 1 x) (N 1 1 x)) / 2) / lam x :=
        div_le_div_of_nonneg_right (abs_metric_pair_le_half (F x) (N 0 0 x) (N 1 1 x))
          hlampos.le
      _ = _ := by dsimp only [q]; ring
  have hG := logarithmicDensity_eq_gauss D hU hx.2 hFs hlams
    (fun y hy => (hconf y hy).1) (fun y hy => (hconf y hy).2)
  change G x = (D.curvatureTensor (F x) u v u v +
    g.euclideanCoefficients (F x) (N 0 0 x) (N 1 1 x) -
    g.euclideanCoefficients (F x) (N 0 1 x) (N 0 1 x)) / lam x at hG
  change ‖G x‖ ≤ B * lam x + (q 0 0 x + q 1 1 x) / 2 + q 0 1 x
  rw [Real.norm_eq_abs, hG, abs_div, abs_of_pos hlampos]
  calc
    _ ≤ (|D.curvatureTensor (F x) u v u v| +
        |g.euclideanCoefficients (F x) (N 0 0 x) (N 1 1 x)| +
        |g.euclideanCoefficients (F x) (N 0 1 x) (N 0 1 x)|) / lam x :=
      div_le_div_of_nonneg_right
        ((abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) hlampos.le
    _ = |D.curvatureTensor (F x) u v u v| / lam x +
        |g.euclideanCoefficients (F x) (N 0 0 x) (N 1 1 x)| / lam x + q 0 1 x := by
      rw [abs_of_nonneg (hpos (N 0 1 x))]
      dsimp only [q]
      ring
    _ ≤ _ := add_le_add (add_le_add hcurvBound hpair) le_rfl

end PoincareConjecture.M65Gauss
