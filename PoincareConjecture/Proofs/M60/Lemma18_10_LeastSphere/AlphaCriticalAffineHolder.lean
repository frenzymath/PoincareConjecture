import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalJetData
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalAffineEquation
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerWeakClassical
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerWeakChain
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerWeakRescaling











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter Metric
open scoped ContDiff Topology

noncomputable section

namespace PoincareConjecture.M60

open Poincare.Analysis.Sobolev.Weak

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

private theorem affineHolder_weak_linear {m : ℕ}
    {u : Plane → EuclideanSpace ℝ (Fin m)}
    {V : Fin 2 → Plane → EuclideanSpace ℝ (Fin m)} {a : Plane} {R r : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hu : MemLp u 4 (volume.restrict (ball a R)))
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict (ball a R)))
    (hw : ∀ i b, HasWeakPartialDeriv i (fun x => V i x b) (fun x => u x b) (ball a R))
    (T : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) (i : Fin 2) (b : Fin m) :
    HasWeakPartialDeriv i (fun x => T (V i x) b) (fun x => T (u x) b) (ball a r) := by
  let L := (EuclideanSpace.proj b).comp T
  have hbound (y : EuclideanSpace ℝ (Fin m)) :
      ‖fderiv ℝ L y‖ ≤ (1 + ‖L‖) * (1 + ‖y‖ ^ 2) := by
    rw [L.fderiv]
    nlinarith [norm_nonneg L, sq_nonneg ‖y‖, mul_nonneg (norm_nonneg L) (sq_nonneg ‖y‖)]
  have h := suWeakPartial_comp_quadratic hr hrR hu hV hw L.contDiff (by positivity) hbound i
  simp only [L.fderiv] at h
  exact h

private theorem affineHolder_weak_smul {O : Set Plane} {u p : Plane → ℝ} {i : Fin 2}
    (hw : HasWeakPartialDeriv i p u O) (c : ℝ) :
    HasWeakPartialDeriv i (fun x => c * p x) (fun x => c * u x) O := by
  intro phi hp hc hs
  simp only [mul_assoc]
  rw [integral_const_mul, integral_const_mul, hw phi hp hc hs, mul_neg]

private theorem affineHolder_ae_rescale (a : Plane) {s : ℝ} (hs : 0 < s)
    (r : ℝ) (P : Plane → Prop) :
    (∀ᵐ x ∂volume.restrict (ball a (s * r)), P x) ↔
      ∀ᵐ z ∂volume.restrict (ball 0 r), P (a + s • z) := by
  have h := (suAffineHomeomorph a hs).toMeasurableEquiv.measurableEmbedding.ae_map_iff
    (μ := volume.restrict ((fun z : Plane => a + s • z) ⁻¹' ball a (s * r))) (p := P)
  change (∀ᵐ x ∂(volume.restrict ((fun z : Plane => a + s • z) ⁻¹' ball a (s * r))).map
    (fun z : Plane => a + s • z), P x) ↔ _ at h
  rw [suAffine_map_restrict a hs, Measure.ae_ennreal_smul_measure_iff (by positivity :
    ENNReal.ofReal ((s ^ 2)⁻¹) ≠ 0), suAffine_preimage_ball a hs] at h
  exact h




theorem suInitialGain_of_transformed_residual_holder :
    ∃ delta : ℝ, 0 < delta ∧ ∀ (m : ℕ)
      {u : Plane → EuclideanSpace ℝ (Fin m)}
      {V : Fin 2 → Plane → EuclideanSpace ℝ (Fin m)} {center : Plane} {R : ℝ}
      (G : SUInitialGain u V center R)
      (T : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m))
      {f : Plane → EuclideanSpace ℝ (Fin m)},
      MemLp f 4 (volume.restrict (ball center (G.radius / 2))) →
      (∀ᵐ x ∂volume.restrict (ball center (G.radius / 2)),
        ‖(∑ i : Fin 2, T (G.hessian i i x)) - f x‖ ≤
          delta * Real.sqrt (∑ i : Fin 2, ∑ j : Fin 2, ‖T (G.hessian i j x)‖ ^ 2)) →
      Nonempty (SUC1HolderGain u V center G.radius) := by
  obtain ⟨delta, C, hd, hC, hregular⟩ := suNearLaplacian_C1_holder
  refine ⟨delta, hd, ?_⟩
  intro m u V center R G T f hf hres
  let s := G.radius / 4
  have hs : 0 < s := div_pos G.radius_pos (by norm_num)
  have hscale : s * 2 = G.radius / 2 := by dsimp [s]; ring
  let A := suAffineHomeomorph center hs
  have hA (z : Plane) : A z = center + s • z := rfl
  let U : Plane → EuclideanSpace ℝ (Fin m) := fun z => T (u (A z))
  let P : Fin 2 → Plane → EuclideanSpace ℝ (Fin m) := fun i z => s • T (V i (A z))
  let H : Fin 2 → Fin 2 → Plane → EuclideanSpace ℝ (Fin m) :=
    fun i j z => s ^ 2 • T (G.hessian i j (A z))
  let F : Plane → EuclideanSpace ℝ (Fin m) := fun z => s ^ 2 • f (A z)
  have hpre : (fun z : Plane => center + s • z) ⁻¹' ball center (G.radius / 2) = ball 0 2 := by
    rw [← hscale, suAffine_preimage_ball center hs]
  have hsub : ball center (G.radius / 2) ⊆ ball center G.radius :=
    ball_subset_ball (half_le_self G.radius_pos.le)
  have hV (i : Fin 2) : MemLp (V i) 2 (volume.restrict (ball center G.radius)) := by
    simpa only [ENNReal.ofReal_ofNat] using G.column_memLp 2 (by norm_num) i
  have hLp {p : ENNReal} {v : Plane → EuclideanSpace ℝ (Fin m)}
      (hv : MemLp v p (volume.restrict (ball center (G.radius / 2)))) :
      MemLp (fun z => T (v (A z))) p (volume.restrict (ball 0 2)) := by
    simpa only [hA, Function.comp_apply, ContinuousLinearEquiv.coe_coe, hpre] using
      suAffine_memLp (T.toContinuousLinearMap.comp_memLp' hv) center hs
  have hU : MemLp U 2 (volume.restrict (ball 0 2)) :=
    hLp (G.coordinate_memLp.mono_measure (Measure.restrict_mono hsub le_rfl))
  have hP (i : Fin 2) : MemLp (P i) 2 (volume.restrict (ball 0 2)) :=
    (hLp ((hV i).mono_measure (Measure.restrict_mono hsub le_rfl))).const_smul s
  have hH (i j : Fin 2) : MemLp (H i j) 2 (volume.restrict (ball 0 2)) :=
    (hLp ((G.hessian_memLp i j).mono_measure
      (Measure.restrict_mono hsub le_rfl))).const_smul (s ^ 2)
  have hF : MemLp F 4 (volume.restrict (ball 0 2)) := by
    have h : MemLp (fun z => f (center + s • z)) 4 (volume.restrict (ball 0 2)) := by
      simpa only [hpre] using suAffine_memLp hf center hs
    change MemLp (fun z => s ^ 2 • f (center + s • z)) 4 (volume.restrict (ball 0 2))
    exact h.const_smul (s ^ 2)
  have hw (i : Fin 2) (b : Fin m) :
      HasWeakPartialDeriv i (fun z => P i z b) (fun z => U z b) (ball 0 2) := by
    have h := affineHolder_weak_linear (half_pos G.radius_pos) (half_lt_self G.radius_pos)
      (suContinuous_memLp_ball G.coordinate_continuous) hV G.weak_derivative
      T.toContinuousLinearMap i b
    simpa only [hpre, P, U, hA, ContinuousLinearEquiv.coe_coe, PiLp.smul_apply,
      smul_eq_mul] using suAffine_weakPartial h center hs
  have hwH (i j : Fin 2) (b : Fin m) :
      HasWeakPartialDeriv j (fun z => H i j z b) (fun z => P i z b) (ball 0 2) := by
    have hv4 : MemLp (V i) 4 (volume.restrict (ball center G.radius)) := by
      simpa only [ENNReal.ofReal_ofNat] using G.column_memLp 4 (by norm_num) i
    have h := affineHolder_weak_linear (half_pos G.radius_pos) (half_lt_self G.radius_pos)
      hv4 (G.hessian_memLp i) (G.second_weak_derivative i) T.toContinuousLinearMap j b
    have h' := affineHolder_weak_smul (suAffine_weakPartial h center hs) s
    simpa only [hpre, H, P, hA, ContinuousLinearEquiv.coe_coe, PiLp.smul_apply,
      smul_eq_mul, pow_two, mul_assoc] using h'
  have hUc : ContinuousOn U (ball 0 2) := by
    apply T.continuous.comp_continuousOn
    apply (G.coordinate_continuous.mono (hsub.trans ball_subset_closedBall)).comp
      A.continuous.continuousOn
    intro z hz
    change center + s • z ∈ ball center (G.radius / 2)
    change z ∈ (fun z : Plane => center + s • z) ⁻¹' ball center (G.radius / 2)
    rwa [hpre]
  have hres' : ∀ᵐ z ∂volume.restrict (ball 0 2),
      ‖(∑ i : Fin 2, H i i z) - F z‖ ≤
        delta * Real.sqrt (∑ i : Fin 2, ∑ j : Fin 2, ‖H i j z‖ ^ 2) := by
    have ha := (affineHolder_ae_rescale center hs 2 _).mp (by simpa only [hscale] using hres)
    filter_upwards [ha] with z hz
    dsimp only [H, F]
    rw [← Finset.smul_sum, ← smul_sub, norm_smul, Real.norm_of_nonneg (sq_nonneg s)]
    have he : (∑ i : Fin 2, ∑ j : Fin 2, ‖s ^ 2 • T (G.hessian i j (A z))‖ ^ 2) =
        (s ^ 2) ^ 2 * ∑ i : Fin 2, ∑ j : Fin 2, ‖T (G.hessian i j (A z))‖ ^ 2 := by
      simp only [norm_smul, Real.norm_of_nonneg (sq_nonneg s), mul_pow, ← Finset.mul_sum]
    rw [he, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (sq_nonneg s)]
    simp only [hA]
    nlinarith [mul_le_mul_of_nonneg_left hz (sq_nonneg s)]
  obtain ⟨hUd, hPeq, hhold⟩ := hregular m hU hP hw hH hwH hF hUc hres'
  let K := C * Real.sqrt (suHessianEnergy H (ball 0 2) + Real.sqrt (∫ z in ball 0 2, ‖F z‖ ^ 4))
  have hK : 0 ≤ K := mul_nonneg hC.le (Real.sqrt_nonneg _)
  have hinv (x : Plane) : A.symm x = s⁻¹ • (x - center) := by
    change s⁻¹ • (-center + x) = _
    congr 1
    abel
  have hundo : (fun x => T.symm (U (A.symm x))) = u := by
    funext x
    simp only [U, A.apply_symm_apply, T.symm_apply_apply]
  have hsource : ContDiff ℝ 1 (fun x => A.symm x) := by
    simp only [hinv]
    exact (contDiff_id.sub contDiff_const).const_smul _
  have hmaps (r : ℝ) : MapsTo A.symm (ball center (s * r)) (ball 0 r) := by
    intro x hx
    have := (suAffine_preimage_ball center hs r)
    have hx' : A (A.symm x) ∈ ball center (s * r) := by simpa using hx
    change A.symm x ∈ (fun z : Plane => center + s • z) ⁻¹' ball center (s * r) at hx'
    rwa [this] at hx'
  have hud : ContDiffOn ℝ 1 u (ball center (s / 4)) := by
    have h := T.symm.contDiff.comp_contDiffOn
      (hUd.comp hsource.contDiffOn (by simpa only [div_eq_mul_inv] using hmaps (1 / 4)))
    change ContDiffOn ℝ 1 (fun x => T.symm (U (A.symm x))) _ at h
    simpa only [hundo, div_eq_mul_inv, one_mul] using h
  have hdU (z : Plane) : fderiv ℝ U z =
      s • (T.toContinuousLinearMap.comp (fderiv ℝ u (A z))) := by
    change fderiv ℝ (T ∘ fun y => u (center + s • y)) z = _
    rw [T.comp_fderiv, suRescale_fderiv]
    rw [ContinuousLinearMap.comp_smul]
    rfl
  have hcol (i : Fin 2) : ∀ᵐ x ∂volume.restrict (ball center (s / 4)),
      fderiv ℝ u x (EuclideanSpace.single i 1) = V i x := by
    rw [show s / 4 = s * (1 / 4) by ring]
    apply (affineHolder_ae_rescale center hs (1 / 4) _).mpr
    filter_upwards [hPeq i] with z hz
    rw [hdU] at hz
    change s • T (fderiv ℝ u (A z) (EuclideanSpace.single i 1)) = s • T (V i (A z)) at hz
    exact T.injective ((smul_right_injective _ hs.ne') hz)
  have hdback (x : Plane) : fderiv ℝ u x =
      s⁻¹ • (T.symm.toContinuousLinearMap.comp (fderiv ℝ U (A.symm x))) := by
    rw [hdU, A.apply_symm_apply]
    apply ContinuousLinearMap.ext
    intro v
    simp only [smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      map_smul, T.symm_apply_apply, inv_smul_smul₀ hs.ne']
  refine ⟨{
    radius := s / 4
    radius_pos := div_pos hs (by norm_num)
    radius_lt := by dsimp [s]; linarith [G.radius_pos]
    coordinate_contDiff := hud
    column_ae := hcol
    constant := s⁻¹ * ‖T.symm.toContinuousLinearMap‖ * K * Real.sqrt (Real.sqrt s⁻¹)
    constant_nonneg := by positivity
    derivative_holder := ?_ }⟩
  intro x hx y hy
  have hin (z : Plane) (hz : z ∈ closedBall center (s / 4 / 2)) :
      A.symm z ∈ closedBall (0 : Plane) (1 / 8) := by
    have him := suRescale_closedBall center hs (1 / 8)
    have hz' : z ∈ (fun w : Plane => center + s • w) '' closedBall 0 (1 / 8) := by
      rw [him]
      simpa only [show s * (1 / 8) = s / 4 / 2 by ring] using hz
    obtain ⟨w, hw, rfl⟩ := hz'
    change A.symm (A w) ∈ closedBall 0 (1 / 8)
    simpa only [A.symm_apply_apply] using hw
  have hb := hhold (A.symm x) (hin x hx) (A.symm y) (hin y hy)
  have hdist : dist (A.symm x) (A.symm y) = s⁻¹ * dist x y := by
    rw [hinv, hinv, dist_eq_norm, ← smul_sub, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hs.le)]
    congr 1
    rw [dist_eq_norm]
    congr 1
    abel
  rw [hdist, Real.sqrt_mul (inv_nonneg.mpr hs.le),
    Real.sqrt_mul (Real.sqrt_nonneg _)] at hb
  have hop : dist (fderiv ℝ u x) (fderiv ℝ u y) ≤
      s⁻¹ * ‖T.symm.toContinuousLinearMap‖ *
        dist (fderiv ℝ U (A.symm x)) (fderiv ℝ U (A.symm y)) := by
    have he : fderiv ℝ u x - fderiv ℝ u y = s⁻¹ • (T.symm.toContinuousLinearMap.comp
        (fderiv ℝ U (A.symm x) - fderiv ℝ U (A.symm y))) := by
      rw [hdback x, hdback y]
      apply ContinuousLinearMap.ext
      intro v
      simp only [sub_apply, ContinuousLinearMap.comp_apply,
        smul_apply, map_sub, smul_sub]
    rw [dist_eq_norm, he, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hs.le)]
    exact (mul_le_mul_of_nonneg_left
      (ContinuousLinearMap.opNorm_comp_le _ _) (inv_nonneg.mpr hs.le)).trans_eq (by
        rw [dist_eq_norm]; ring)
  exact hop.trans ((mul_le_mul_of_nonneg_left hb
    (mul_nonneg (inv_nonneg.mpr hs.le) (norm_nonneg _))).trans_eq (by dsimp only [K]; ring))

attribute [local instance] affineJetPrincipalNormedGroup affineJetPrincipalNormedSpace
  affineJetSourceNormedGroup affineJetSourceNormedSpace

local instance affineHolderOffsetDerivativeNormedGroup {m : ℕ} :
    NormedAddCommGroup ((Plane × EuclideanSpace ℝ (Fin m)) →L[ℝ]
      (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance affineHolderOffsetDerivativeNormedSpace {m : ℕ} :
    NormedSpace ℝ ((Plane × EuclideanSpace ℝ (Fin m)) →L[ℝ]
      (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

set_option maxHeartbeats 800000 in




theorem suAffineJet_lowerTrace_memLp {m : ℕ}
    {u : Plane → EuclideanSpace ℝ (Fin m)}
    {V : Fin 2 → Plane → EuclideanSpace ℝ (Fin m)} {center : Plane} {R : ℝ}
    (G : SUInitialGain u V center R) (C : SUAffineJetCoefficients m)
    {O : Set (Plane × EuclideanSpace ℝ (Fin m))} (hO : IsOpen O)
    (hmap : MapsTo (fun x => (x, u x)) (closedBall center G.radius) O)
    (hA : ContDiffOn ℝ 1 C.principal O) (hc : ContDiffOn ℝ 1 C.fluxOffset O)
    (hB : ContinuousOn C.sourceLinear O) (hd : ContinuousOn C.sourceOffset O) :
    MemLp (fun x => C.lowerTrace (x, u x) (fun i => V i x)) 4
      (volume.restrict (ball center G.radius)) := by
  classical
  let E := EuclideanSpace ℝ (Fin m)
  let Q := E × E
  let B := Plane × E
  let mu := volume.restrict (ball center G.radius)
  let : ENNReal.HolderTriple 8 8 4 := ENNReal.HolderTriple.of_toReal (by
    norm_num only [ENNReal.toReal_ofNat]
    exact ⟨by norm_num, by norm_num, by norm_num⟩)
  have hz : ContinuousOn (fun x => (x, u x)) (closedBall center G.radius) :=
    continuousOn_id.prodMk G.coordinate_continuous
  have hq (p : ℝ) (hp : 1 ≤ p) :
      MemLp (fun x => (V 0 x, V 1 x)) (ENNReal.ofReal p) mu :=
    memLp_prod_iff.mpr ⟨G.column_memLp p hp 0, G.column_memLp p hp 1⟩
  have hq4 : MemLp (fun x => (V 0 x, V 1 x)) 4 mu := by
    simpa only [ENNReal.ofReal_ofNat] using hq 4 (by norm_num)
  have hq8 : MemLp (fun x => (V 0 x, V 1 x)) 8 mu := by
    simpa only [ENNReal.ofReal_ofNat] using hq 8 (by norm_num)
  have hb (p : ℝ) (hp : 1 ≤ p) (i : Fin 2) :
      MemLp (fun x => (EuclideanSpace.single i (1 : ℝ), V i x)) (ENNReal.ofReal p) mu :=
    memLp_prod_iff.mpr ⟨suContinuous_memLp_ball continuousOn_const, G.column_memLp p hp i⟩
  have hb4 (i : Fin 2) : MemLp (fun x => (EuclideanSpace.single i (1 : ℝ), V i x)) 4 mu := by
    simpa only [ENNReal.ofReal_ofNat] using hb 4 (by norm_num) i
  have hb8 (i : Fin 2) : MemLp (fun x => (EuclideanSpace.single i (1 : ℝ), V i x)) 8 mu := by
    simpa only [ENNReal.ofReal_ofNat] using hb 8 (by norm_num) i
  have hDA : MemLp (fun x => fderiv ℝ C.principal (x, u x)) ⊤ mu :=
    suContinuous_memLp_ball
      ((hA.continuousOn_fderiv_of_isOpen hO (by norm_num)).comp hz hmap)
  have hDc : MemLp (fun x => fderiv ℝ C.fluxOffset (x, u x)) ⊤ mu :=
    suContinuous_memLp_ball
      ((hc.continuousOn_fderiv_of_isOpen hO (by norm_num)).comp hz hmap)
  have hBL : MemLp (fun x => C.sourceLinear (x, u x)) ⊤ mu :=
    suContinuous_memLp_ball (hB.comp hz hmap)
  have hdL : MemLp (fun x => C.sourceOffset (x, u x)) 4 mu :=
    suContinuous_memLp_ball (hd.comp hz hmap)
  have hsource : MemLp (fun x => C.source (x, u x) (V 0 x, V 1 x)) 4 mu :=
    ((ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) (E := Q)).memLp_of_bilin
      (p := 4) (q := ⊤) 4 hq4 hBL).add hdL
  have hterm (i : Fin 2) : MemLp (fun x =>
      fderiv ℝ C.principal (x, u x) (EuclideanSpace.single i 1, V i x) (V 0 x, V 1 x) +
        fderiv ℝ C.fluxOffset (x, u x) (EuclideanSpace.single i 1, V i x)) 4 mu := by
    have hfirst : MemLp (fun x =>
        fderiv ℝ C.principal (x, u x) (EuclideanSpace.single i 1, V i x)) 8 mu := by
      let ev : B →L[ℝ] (B →L[ℝ] Q →L[ℝ] Q →L[ℝ] ℝ) →L[ℝ] Q →L[ℝ] Q →L[ℝ] ℝ :=
        ContinuousLinearMap.apply ℝ (Q →L[ℝ] Q →L[ℝ] ℝ)
      exact ev.memLp_of_bilin (p := 8) (q := ⊤) 8 (hb8 i) hDA
    have hsecond : MemLp (fun x =>
        fderiv ℝ C.fluxOffset (x, u x) (EuclideanSpace.single i 1, V i x)) 4 mu := by
      let ev : B →L[ℝ] (B →L[ℝ] Q →L[ℝ] ℝ) →L[ℝ] Q →L[ℝ] ℝ :=
        ContinuousLinearMap.apply ℝ (Q →L[ℝ] ℝ)
      exact ev.memLp_of_bilin (p := 4) (q := ⊤) 4 (hb4 i) hDc
    exact ((ContinuousLinearMap.apply ℝ (Q →L[ℝ] ℝ) (E := Q)).memLp_of_bilin
      (p := 8) (q := 8) 4 hq8 hfirst).add hsecond
  apply MemLp.of_eval_piLp
  intro a
  have hs := (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single a 1)).comp_memLp' hsource
  have ht (i : Fin 2) :=
    (ContinuousLinearMap.apply ℝ ℝ (suColumnBasis a i)).comp_memLp' (hterm i)
  exact hs.add (memLp_finsetSum _ (fun i _ => ht i))




theorem suAffineJet_holder_of_trace :
    ∃ delta : ℝ, 0 < delta ∧ ∀ (m : ℕ)
      {u : Plane → EuclideanSpace ℝ (Fin m)}
      {V : Fin 2 → Plane → EuclideanSpace ℝ (Fin m)} {center : Plane} {R : ℝ}
      (G : SUInitialGain u V center R) (C : SUAffineJetCoefficients m)
      {O : Set (Plane × EuclideanSpace ℝ (Fin m))}, IsOpen O →
      MapsTo (fun x => (x, u x)) (closedBall center G.radius) O →
      ContDiffOn ℝ 1 C.principal O → ContDiffOn ℝ 1 C.fluxOffset O →
      ContinuousOn C.sourceLinear O → ContinuousOn C.sourceOffset O →
      SUAffineJetNormalization C O delta →
      (∀ᵐ x ∂volume.restrict (ball center (G.radius / 2)),
        C.principalTrace (x, u x) (fun i j => G.hessian i j x) +
          C.lowerTrace (x, u x) (fun i => V i x) = 0) →
      Nonempty (SUC1HolderGain u V center G.radius) := by
  obtain ⟨delta, hd, hgain⟩ := suInitialGain_of_transformed_residual_holder
  refine ⟨delta, hd, ?_⟩
  intro m u V center R G C O hO hmap hA hc hB hd N heq
  let f (x : Plane) := -N.targetChange (N.normalizer (x, u x)
    (C.lowerTrace (x, u x) (fun i => V i x)))
  have hz := continuousOn_id.prodMk G.coordinate_continuous
  have hN : MemLp (fun x => N.normalizer (x, u x)) ⊤
      (volume.restrict (ball center G.radius)) :=
    suContinuous_memLp_ball (N.normalizer_smooth.continuousOn.comp hz hmap)
  have hf0 := ((N.targetChange.toContinuousLinearMap).comp_memLp'
    ((ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin m))
      (E := EuclideanSpace ℝ (Fin m))).memLp_of_bilin (p := 4) (q := ⊤) 4
        (suAffineJet_lowerTrace_memLp G C hO hmap hA hc hB hd) hN)).neg
  have hf : MemLp f 4 (volume.restrict (ball center (G.radius / 2))) :=
    hf0.mono_measure (Measure.restrict_mono
      (ball_subset_ball (half_le_self G.radius_pos.le)) le_rfl)
  apply hgain m G N.targetChange hf
  filter_upwards [heq, ae_restrict_mem measurableSet_ball] with x hx hxin
  have hb := N.residual_bound (x, u x)
    (hmap ((ball_subset_closedBall.trans (closedBall_subset_closedBall
      (half_le_self G.radius_pos.le))) hxin)) (fun i j => G.hessian i j x)
  have he : C.principalTrace (x, u x) (fun i j => G.hessian i j x) =
      -C.lowerTrace (x, u x) (fun i => V i x) := eq_neg_of_add_eq_zero_left hx
  simpa only [he, map_sub, map_sum, map_neg, f, sub_neg_eq_add, map_add] using hb





theorem suAffineQuadraticSystem_holder :
    ∃ delta : ℝ, 0 < delta ∧ ∀ (m : ℕ)
      {u : Plane → EuclideanSpace ℝ (Fin m)}
      {V : Fin 2 → Plane → EuclideanSpace ℝ (Fin m)} {center : Plane} {R : ℝ}
      (S : SUQuadraticWeakSystem u V center R) (C : SUAffineJetCoefficients m),
      S.flux = C.flux → S.source = C.source →
      ∀ (G : SUInitialGain u V center R)
      {O : Set (Plane × EuclideanSpace ℝ (Fin m))}, IsOpen O →
      MapsTo (fun x => (x, u x)) (closedBall center G.radius) O →
      ContDiffOn ℝ 1 C.principal O → ContDiffOn ℝ 1 C.fluxOffset O →
      ContinuousOn C.sourceLinear O → ContinuousOn C.sourceOffset O →
      SUAffineJetNormalization C O delta → Nonempty (SUC1HolderGain u V center G.radius) := by
  obtain ⟨delta, hd, hholder⟩ := suAffineJet_holder_of_trace
  refine ⟨delta, hd, ?_⟩
  intro m u V center R S C hflux hsource G O hO hmap hA hc hB hd N
  exact hholder m G C hO hmap hA hc hB hd N
    (suAffineWeakEquation_trace S C hflux hsource G hO hmap hA hc)

end PoincareConjecture.M60
