import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerSlicing
import PoincareConjecture.Proofs.M03.Existence.DeTurckDomainRegularityNative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Topology SchwartzMap LineDeriv InnerProductSpace ContDiff ENNReal

namespace PoincareConjecture

open EuclideanTranslationNative EuclideanMollificationNative DeTurckDomainRegularityNative

private theorem m65Product_vertical_line (x y : ℝ) :
    Proofs.M58.loopPlaneEquivProd.symm (x, y) =
      EuclideanSpace.single 0 x + y • EuclideanSpace.single 1 (1 : ℝ) := by
  ext i
  fin_cases i
  · change x = x + y * 0
    ring
  · change y = 0 + y * 1
    ring

theorem m65WeakPair_vertical_AC
    (u d : Lp ℝ 2 (volume : Measure LoopPlane))
    (hweak : ∀ φ : 𝓢(LoopPlane, ℝ), ⟪d, φ.toLp 2 volume⟫_ℝ =
      -(∫ z, u z * fderiv ℝ φ z (EuclideanSpace.single 1 (1 : ℝ))))
    {a b : ℝ} (hab : a < b) :
    ∀ᵐ x ∂(volume : Measure ℝ), ∃ v : ℝ → ℝ,
      AbsolutelyContinuousOnInterval v a b ∧
      (v =ᵐ[volume.restrict (Icc a b)]
        fun y => u (Proofs.M58.loopPlaneEquivProd.symm (x, y))) ∧
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        v t - v s = ∫ y in s..t, d (Proofs.M58.loopPlaneEquivProd.symm (x, y)) := by
  let nu : Measure (ℝ × ℝ) := volume.prod (volume.restrict (Icc a b))
  let full : Measure (ℝ × ℝ) := volume.prod volume
  have hle : nu ≤ full := Measure.prod_mono le_rfl Measure.restrict_le_self
  have hmul : nu ≤ (1 : ℝ≥0∞) • full := by simpa only [one_smul] using hle
  let P : Lp ℝ 2 (volume : Measure LoopPlane) →L[ℝ] Lp ℝ 2 full :=
    (Lp.compMeasurePreservingₗᵢ ℝ Proofs.M58.loopPlaneEquivProd.symm
      Proofs.M58.measurePreserving_loopPlaneEquivProd.symm).toContinuousLinearMap
  let R : Lp ℝ 2 full →L[ℝ] Lp ℝ 2 nu :=
    Lp.LpToLpOfMeasureLeSMul (by simp : (1 : ℝ≥0∞) ≠ ⊤) hmul
  let T := R.comp P
  have hT (w : Lp ℝ 2 (volume : Measure LoopPlane)) :
      T w =ᵐ[nu] fun p => w (Proofs.M58.loopPlaneEquivProd.symm p) := by
    exact (Lp.coeFn_LpToLpOfMeasureLeSMul (by simp : (1 : ℝ≥0∞) ≠ ⊤) hmul (P w)).trans
      ((Measure.absolutelyContinuous_of_le hle).ae_eq
        (Lp.coeFn_compMeasurePreserving w Proofs.M58.measurePreserving_loopPlaneEquivProd.symm))
  have hcomp {f g : LoopPlane → ℝ} (hfg : f =ᵐ[volume] g) :
      (fun p => f (Proofs.M58.loopPlaneEquivProd.symm p)) =ᵐ[nu]
        fun p => g (Proofs.M58.loopPlaneEquivProd.symm p) :=
    (Measure.absolutelyContinuous_of_le hle).ae_eq
      (Proofs.M58.measurePreserving_loopPlaneEquivProd.symm.quasiMeasurePreserving.ae hfg)
  let eps (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have heps (n : ℕ) : 0 < eps n := by dsimp only [eps]; positivity
  have heps0 : Tendsto eps atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  let f (n : ℕ) (x y : ℝ) :=
    mollify (heps n) u (Proofs.M58.loopPlaneEquivProd.symm (x, y))
  have hf (n : ℕ) (x : ℝ) : ContDiff ℝ 1 (f n x) := by
    have hline : ContDiff ℝ 1 (fun y : ℝ =>
        (EuclideanSpace.single 0 x : LoopPlane) + y • EuclideanSpace.single 1 (1 : ℝ)) :=
      contDiff_const.add (contDiff_id.smul contDiff_const)
    have hm : ContDiff ℝ 1 (mollify (heps n) u) :=
      (contDiff_mollify (heps n) u).of_le (by simp)
    have hh := hm.comp hline
    simpa only [f, m65Product_vertical_line, Function.comp_def] using hh
  have hfd (n : ℕ) (x y : ℝ) :
      deriv (f n x) y = mollify (heps n) d (Proofs.M58.loopPlaneEquivProd.symm (x, y)) := by
    have hline : HasDerivAt (fun t : ℝ =>
        (EuclideanSpace.single 0 x : LoopPlane) + t • EuclideanSpace.single 1 (1 : ℝ))
        (EuclideanSpace.single 1 (1 : ℝ)) y := by
      simpa only [one_smul, id_eq] using ((hasDerivAt_id y).smul_const
        (EuclideanSpace.single 1 (1 : ℝ) : LoopPlane)).const_add (EuclideanSpace.single 0 x)
    have hmd := (contDiff_mollify (heps n) u).differentiable (by simp)
    have hh := (hmd _).hasFDerivAt.comp_hasDerivAt y hline
    have hactual := hh.deriv
    simpa only [f, m65Product_vertical_line, Function.comp_def,
      fderiv_mollify_of_weak_pairing (heps n) u d _ hweak] using hactual
  have hfu (n : ℕ) : T (mollifyL2 (heps n) u) =ᵐ[nu] fun p => f n p.1 p.2 :=
    (hT _).trans (hcomp (mollifyL2_ae_eq (heps n) u))
  have hfd' (n : ℕ) : T (mollifyL2 (heps n) d) =ᵐ[nu]
      fun p => deriv (f n p.1) p.2 := by
    simpa only [hfd] using (hT _).trans (hcomp (mollifyL2_ae_eq (heps n) d))
  have hUconv := (T.continuous.tendsto u).comp (tendsto_mollifyL2 eps heps heps0 u)
  have hDconv := (T.continuous.tendsto d).comp (tendsto_mollifyL2 eps heps heps0 d)
  have hAC := m65Product_AC_of_smooth_L2_graph hab f hf
    (fun n => T (mollifyL2 (heps n) u)) (fun n => T (mollifyL2 (heps n) d))
    (T u) (T d) hfu hfd' hUconv hDconv
  filter_upwards [hAC, Measure.ae_ae_of_ae_prod (hT u),
    Measure.ae_ae_of_ae_prod (hT d)] with x hx hux hdx
  obtain ⟨v, hv, hvu, hvd⟩ := hx
  refine ⟨v, hv, hvu.trans hux, ?_⟩
  intro s hs t ht
  rw [hvd s hs t ht]
  apply intervalIntegral.integral_congr_ae_restrict
  exact ae_restrict_of_ae_restrict_of_subset
    ((uIoc_subset_uIcc).trans (uIcc_subset_Icc hs ht)) hdx

end PoincareConjecture
