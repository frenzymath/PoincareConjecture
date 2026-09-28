import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalJetData
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerSourceWeakChain









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Metric
open scoped ContDiff Topology ENNReal
open Poincare.Analysis.Sobolev.Weak

noncomputable section

namespace PoincareConjecture.M60

private abbrev E (m : ℕ) := EuclideanSpace ℝ (Fin m)
private abbrev Grad (m : ℕ) := E m × E m
private abbrev Base (m : ℕ) := LoopPlane × E m

local instance affineSystemBilinearNormedGroup {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup

local instance affineSystemBilinearNormedSpace {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    NormedSpace ℝ (F →L[ℝ] F →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

local instance affineSystemMixedNormedGroup {m : ℕ} :
    NormedAddCommGroup (Grad m →L[ℝ] E m →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance affineSystemMixedNormedSpace {m : ℕ} :
    NormedSpace ℝ (Grad m →L[ℝ] E m →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace



theorem suCompactCoefficient_bound
    {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Set P}
    (hK : IsCompact K) (hconv : Convex ℝ K) {f : P → F}
    (hf : ∀ x ∈ K, ContDiffAt ℝ 1 f x) :
    ∃ C : ℝ, 0 < C ∧ (∀ x ∈ K, ‖f x‖ ≤ C) ∧
      ∀ x ∈ K, ∀ y ∈ K, ‖f y - f x‖ ≤ C * ‖y - x‖ := by
  obtain ⟨C0, hC0⟩ := hK.exists_bound_of_continuousOn
    (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
  obtain ⟨C1, hC1⟩ := hK.exists_bound_of_continuousOn
    (fun x hx => ((hf x hx).continuousAt_fderiv (by norm_num)).continuousWithinAt)
  let C := 1 + |C0| + |C1|
  have hC : 0 < C := by dsimp [C]; positivity
  have h0 : C0 ≤ C := by dsimp [C]; linarith [le_abs_self C0, abs_nonneg C1]
  have h1 : C1 ≤ C := by dsimp [C]; linarith [le_abs_self C1, abs_nonneg C0]
  refine ⟨C, hC, fun x hx => (hC0 x hx).trans h0, fun x hx y hy => ?_⟩
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (hf z hz).differentiableAt (by norm_num))
    (fun z hz => (hC1 z hz).trans h1) hconv hx hy



theorem suScalarEquations_vectorEquation {m : ℕ} {center : LoopPlane} {R : ℝ}
    {F : LoopPlane → Grad m →L[ℝ] ℝ} {B : LoopPlane → E m →L[ℝ] ℝ}
    (hF : MemLp F 2 (volume.restrict (ball center R)))
    (hB : MemLp B 2 (volume.restrict (ball center R)))
    (heq : ∀ (a : Fin m) (phi : LoopPlane → ℝ),
      ContDiff ℝ ∞ phi → HasCompactSupport phi → tsupport phi ⊆ ball center R →
      (∫ x in ball center R, ∑ i : Fin 2,
        F x (suColumnBasis a i) * fderiv ℝ phi x (EuclideanSpace.single i 1)) =
        ∫ x in ball center R, B x (EuclideanSpace.single a 1) * phi x)
    {phi : LoopPlane → E m} (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (hs : tsupport phi ⊆ ball center R) :
    (∫ x in ball center R, F x (fderiv ℝ phi x (EuclideanSpace.single 0 1),
      fderiv ℝ phi x (EuclideanSpace.single 1 1))) =
      ∫ x in ball center R, B x (phi x) := by
  classical
  let p (a : Fin m) (x : LoopPlane) := phi x a
  have hp' (a : Fin m) : ContDiff ℝ ∞ (p a) := by
    change ContDiff ℝ ∞ ((EuclideanSpace.proj (𝕜 := ℝ) a) ∘ phi)
    exact (EuclideanSpace.proj a).contDiff.comp hp
  have hc' (a : Fin m) : HasCompactSupport (p a) :=
    hc.comp_left (EuclideanSpace.proj a).map_zero
  have hs' (a : Fin m) : tsupport (p a) ⊆ ball center R :=
    (tsupport_comp_subset (g := EuclideanSpace.proj a) (map_zero _) phi).trans hs
  have hd (a : Fin m) (i : Fin 2) (x : LoopPlane) :
      fderiv ℝ (p a) x (EuclideanSpace.single i 1) =
        fderiv ℝ phi x (EuclideanSpace.single i 1) a := by
    exact congrArg (fun L => L (EuclideanSpace.single i 1))
      (((EuclideanSpace.proj a).hasFDerivAt.comp x
        (hp.differentiable (by simp) x).hasFDerivAt).fderiv)
  have hFI (a : Fin m) (i : Fin 2) : IntegrableOn
      (fun x => F x (suColumnBasis a i) *
        fderiv ℝ (p a) x (EuclideanSpace.single i 1)) (ball center R) := by
    have hv : MemLp (fun x => fderiv ℝ (p a) x (EuclideanSpace.single i 1)) 2
        (volume.restrict (ball center R)) :=
      suContinuous_memLp_ball (((hp' a).continuous_fderiv (by simp)).clm_apply continuous_const
        |>.continuousOn)
    exact memLp_one_iff_integrable.mp
      (hv.mul' ((ContinuousLinearMap.apply ℝ ℝ (suColumnBasis a i)).comp_memLp' hF))
  have hBI (a : Fin m) : IntegrableOn
      (fun x => B x (EuclideanSpace.single a 1) * p a x) (ball center R) := by
    have hv : MemLp (p a) 2 (volume.restrict (ball center R)) :=
      suContinuous_memLp_ball (hp' a).continuous.continuousOn
    exact memLp_one_iff_integrable.mp (hv.mul'
      ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single a (1 : ℝ))).comp_memLp' hB))
  calc
    _ = ∫ x in ball center R, ∑ a : Fin m, ∑ i : Fin 2,
        F x (suColumnBasis a i) * fderiv ℝ (p a) x (EuclideanSpace.single i 1) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        simp only [hd]
        exact (suColumnDual_pairing (F x)
          (fun i => fderiv ℝ phi x (EuclideanSpace.single i 1))).symm
    _ = ∑ a : Fin m, ∫ x in ball center R, ∑ i : Fin 2,
        F x (suColumnBasis a i) * fderiv ℝ (p a) x (EuclideanSpace.single i 1) :=
      integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun i _ => hFI a i))
    _ = ∑ a : Fin m, ∫ x in ball center R, B x (EuclideanSpace.single a 1) * p a x := by
      apply Finset.sum_congr rfl
      intro a _
      exact heq a (p a) (hp' a) (hc' a) (hs' a)
    _ = ∫ x in ball center R, ∑ a : Fin m, B x (EuclideanSpace.single a 1) * p a x :=
      (integral_finsetSum _ (fun a _ => hBI a)).symm
    _ = _ := integral_congr_ae (Eventually.of_forall fun x =>
      suCoordinateDual_pairing (B x) (phi x))




theorem suAffineQuadraticSystem {m : ℕ}
    (C : SUAffineJetCoefficients m) {u : LoopPlane → E m}
    {V : Fin 2 → LoopPlane → E m} {center : LoopPlane} {R delta nu : ℝ}
    (hR : 0 < R) (hdelta : 0 < delta) (hnu : 0 < nu)
    (hu : ContinuousOn u (closedBall center R))
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict (ball center R)))
    (hw : ∀ i a, HasWeakPartialDeriv i (fun x => V i x a) (fun x => u x a)
      (ball center R))
    (hrange : MapsTo u (closedBall center R) (ball (u center) (delta / 2)))
    (hA : ∀ z ∈ closedBall center R ×ˢ closedBall (u center) delta,
      ContDiffAt ℝ 1 C.principal z)
    (hc : ∀ z ∈ closedBall center R ×ˢ closedBall (u center) delta,
      ContDiffAt ℝ 1 C.fluxOffset z)
    (hB : ∀ z ∈ closedBall center R ×ˢ closedBall (u center) delta,
      ContDiffAt ℝ 1 C.sourceLinear z)
    (hd : ∀ z ∈ closedBall center R ×ˢ closedBall (u center) delta,
      ContDiffAt ℝ 1 C.sourceOffset z)
    (hcoercive : ∀ z ∈ closedBall center R ×ˢ closedBall (u center) delta,
      ∀ q, nu * ‖q‖ ^ 2 ≤ C.principal z q q)
    (heq : ∀ (a : Fin m) (phi : LoopPlane → ℝ),
      ContDiff ℝ ∞ phi → HasCompactSupport phi → tsupport phi ⊆ ball center R →
      (∫ x in ball center R, ∑ i : Fin 2,
        C.flux (x, u x) (V 0 x, V 1 x) (suColumnBasis a i) *
          fderiv ℝ phi x (EuclideanSpace.single i 1)) =
        ∫ x in ball center R,
          C.source (x, u x) (V 0 x, V 1 x) (EuclideanSpace.single a 1) * phi x) :
    ∃ S : SUQuadraticWeakSystem u V center R, S.flux = C.flux ∧ S.source = C.source := by
  classical
  let K := closedBall center R ×ˢ closedBall (u center) delta
  let T (z : Base m) := ((C.principal z, C.fluxOffset z),
    (C.sourceLinear z, C.sourceOffset z))
  have hT (z : Base m) (hz : z ∈ K) : ContDiffAt ℝ 1 T z :=
    ((hA z hz).prodMk (hc z hz)).prodMk ((hB z hz).prodMk (hd z hz))
  obtain ⟨L, hL, hval, hlip⟩ := suCompactCoefficient_bound
    ((isCompact_closedBall center R).prod (isCompact_closedBall (u center) delta))
    ((convex_closedBall center R).prod (convex_closedBall (u center) delta)) hT
  have hAv (z : Base m) (hz : z ∈ K) : ‖C.principal z‖ ≤ L :=
    (norm_fst_le (T z).1).trans ((norm_fst_le (T z)).trans (hval z hz))
  have hcv (z : Base m) (hz : z ∈ K) : ‖C.fluxOffset z‖ ≤ L :=
    (norm_snd_le (T z).1).trans ((norm_fst_le (T z)).trans (hval z hz))
  have hBv (z : Base m) (hz : z ∈ K) : ‖C.sourceLinear z‖ ≤ L :=
    (norm_fst_le (T z).2).trans ((norm_snd_le (T z)).trans (hval z hz))
  have hdv (z : Base m) (hz : z ∈ K) : ‖C.sourceOffset z‖ ≤ L :=
    (norm_snd_le (T z).2).trans ((norm_snd_le (T z)).trans (hval z hz))
  have hAl (x : Base m) (hx : x ∈ K) (y : Base m) (hy : y ∈ K) :
      ‖C.principal y - C.principal x‖ ≤ L * ‖y - x‖ :=
    (norm_fst_le (T y - T x).1).trans ((norm_fst_le (T y - T x)).trans (hlip x hx y hy))
  have hcl (x : Base m) (hx : x ∈ K) (y : Base m) (hy : y ∈ K) :
      ‖C.fluxOffset y - C.fluxOffset x‖ ≤ L * ‖y - x‖ :=
    (norm_snd_le (T y - T x).1).trans ((norm_fst_le (T y - T x)).trans (hlip x hx y hy))
  have hBl (x : Base m) (hx : x ∈ K) (y : Base m) (hy : y ∈ K) :
      ‖C.sourceLinear y - C.sourceLinear x‖ ≤ L * ‖y - x‖ :=
    (norm_fst_le (T y - T x).2).trans ((norm_snd_le (T y - T x)).trans (hlip x hx y hy))
  have hdl (x : Base m) (hx : x ∈ K) (y : Base m) (hy : y ∈ K) :
      ‖C.sourceOffset y - C.sourceOffset x‖ ≤ L * ‖y - x‖ :=
    (norm_snd_le (T y - T x).2).trans ((norm_snd_le (T y - T x)).trans (hlip x hx y hy))
  have hbase : MapsTo (fun x => (x, u x)) (closedBall center R) K := by
    intro x hx
    exact ⟨hx, mem_closedBall.mpr ((mem_ball.mp (hrange hx)).le.trans (by linarith))⟩
  have hTc : ContinuousOn (fun x => T (x, u x)) (closedBall center R) :=
    (show ContinuousOn T K from fun z hz => (hT z hz).continuousAt.continuousWithinAt).comp
      (continuousOn_id.prodMk hu) hbase
  let mu := volume.restrict (ball center R)
  have hq : MemLp (fun x => (V 0 x, V 1 x)) 2 mu := memLp_prod_iff.mpr ⟨hV 0, hV 1⟩
  have hFI : MemLp (fun x => C.flux (x, u x) (V 0 x, V 1 x)) 2 mu :=
    ((ContinuousLinearMap.apply ℝ (Grad m →L[ℝ] ℝ) (E := Grad m)).memLp_of_bilin
      (p := 2) (q := ⊤) 2 hq (suContinuous_memLp_ball hTc.fst.fst)).add
        (suContinuous_memLp_ball hTc.fst.snd)
  have hBI : MemLp (fun x => C.source (x, u x) (V 0 x, V 1 x)) 2 mu :=
    ((ContinuousLinearMap.apply ℝ (E m →L[ℝ] ℝ) (E := Grad m)).memLp_of_bilin
      (p := 2) (q := ⊤) 2 hq (suContinuous_memLp_ball hTc.snd.fst)).add
        (suContinuous_memLp_ball hTc.snd.snd)
  have hfg (z : Base m) (q r : Grad m) :
      C.flux z q - C.flux z r = C.principal z (q - r) := by
    simp only [SUAffineJetCoefficients.flux, map_sub]
    abel
  have hbg (z : Base m) (q r : Grad m) :
      C.source z q - C.source z r = C.sourceLinear z (q - r) := by
    simp only [SUAffineJetCoefficients.source, map_sub]
    abel
  refine ⟨{
    radius_pos := hR
    coordinate_continuous := hu
    coordinate_memLp := suContinuous_memLp_ball hu
    column_memLp := hV
    weak_derivative := hw
    targetRadius := delta
    targetRadius_pos := hdelta
    coordinate_range := hrange
    flux := C.flux
    source := C.source
    nu := nu
    constant := 2 * L
    nu_pos := hnu
    constant_pos := by positivity
    flux_continuous := ?_
    source_continuous := ?_
    flux_bound := ?_
    source_bound := ?_
    flux_monotone := ?_
    flux_gradient_bound := ?_
    flux_base_bound := ?_
    source_gradient_bound := ?_
    source_base_bound := ?_
    flux_integrable := ?_
    source_integrable := ?_
    equation := ?_
  }, rfl, rfl⟩
  · intro z hz
    exact ((((hA z.1 hz.1).continuousAt.comp continuousAt_fst).clm_apply continuousAt_snd).add
      ((hc z.1 hz.1).continuousAt.comp continuousAt_fst)).continuousWithinAt
  · intro z hz
    exact ((((hB z.1 hz.1).continuousAt.comp continuousAt_fst).clm_apply continuousAt_snd).add
      ((hd z.1 hz.1).continuousAt.comp continuousAt_fst)).continuousWithinAt
  · intro z hz q
    have ht := (norm_add_le (C.principal z q) (C.fluxOffset z)).trans
      (add_le_add ((C.principal z).le_opNorm q) (hcv z hz))
    have hm := mul_le_mul_of_nonneg_right (hAv z hz) (norm_nonneg q)
    dsimp only [SUAffineJetCoefficients.flux]
    nlinarith [norm_nonneg q]
  · intro z hz q
    have ht := (norm_add_le (C.sourceLinear z q) (C.sourceOffset z)).trans
      (add_le_add ((C.sourceLinear z).le_opNorm q) (hdv z hz))
    have hm := mul_le_mul_of_nonneg_right (hBv z hz) (norm_nonneg q)
    have hq' : 1 + ‖q‖ ≤ 2 * (1 + ‖q‖ ^ 2) := by nlinarith [sq_nonneg (‖q‖ - 1)]
    have hm' := mul_le_mul_of_nonneg_left hq' hL.le
    dsimp only [SUAffineJetCoefficients.source]
    nlinarith
  · intro z hz q r
    rw [hfg]
    exact hcoercive z hz (q - r)
  · intro z hz q r
    rw [hfg]
    exact ((C.principal z).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right ((hAv z hz).trans (by linarith)) (norm_nonneg _))
  · intro x hx y hy q
    have he : C.flux y q - C.flux x q =
        (C.principal y - C.principal x) q + (C.fluxOffset y - C.fluxOffset x) := by
      simp only [SUAffineJetCoefficients.flux, sub_apply]
      abel
    rw [he]
    have ht := (norm_add_le _ _).trans
      (add_le_add ((C.principal y - C.principal x).le_opNorm q) (hcl x hx y hy))
    have hm := mul_le_mul_of_nonneg_right (hAl x hx y hy) (norm_nonneg q)
    nlinarith [mul_nonneg (norm_nonneg q) (norm_nonneg (y - x)), norm_nonneg (y - x)]
  · intro z hz q r
    rw [hbg]
    have ht := ((C.sourceLinear z).le_opNorm (q - r)).trans
      (mul_le_mul_of_nonneg_right (hBv z hz) (norm_nonneg (q - r)))
    exact ht.trans (mul_le_mul_of_nonneg_right
      (by nlinarith [norm_nonneg q, norm_nonneg r]) (norm_nonneg _))
  · intro x hx y hy q
    have he : C.source y q - C.source x q =
        (C.sourceLinear y - C.sourceLinear x) q +
          (C.sourceOffset y - C.sourceOffset x) := by
      simp only [SUAffineJetCoefficients.source, sub_apply]
      abel
    rw [he]
    have ht := (norm_add_le _ _).trans
      (add_le_add ((C.sourceLinear y - C.sourceLinear x).le_opNorm q) (hdl x hx y hy))
    have hm := mul_le_mul_of_nonneg_right (hBl x hx y hy) (norm_nonneg q)
    have hq' : 1 + ‖q‖ ≤ 2 * (1 + ‖q‖ ^ 2) := by nlinarith [sq_nonneg (‖q‖ - 1)]
    have hm' := mul_le_mul_of_nonneg_left hq' (mul_nonneg hL.le (norm_nonneg (y - x)))
    nlinarith
  · intro phi hp _ _
    have hdphi : MemLp (fun x => (fderiv ℝ phi x (EuclideanSpace.single 0 1),
        fderiv ℝ phi x (EuclideanSpace.single 1 1))) 2 mu :=
      suContinuous_memLp_ball
        (((hp.continuous_fderiv (by simp)).clm_apply continuous_const).prodMk
          ((hp.continuous_fderiv (by simp)).clm_apply continuous_const)).continuousOn
    exact memLp_one_iff_integrable.mp
      ((ContinuousLinearMap.apply ℝ ℝ (E := Grad m)).memLp_of_bilin 1 hdphi hFI)
  · intro phi hp _ _
    exact memLp_one_iff_integrable.mp
      ((ContinuousLinearMap.apply ℝ ℝ (E := E m)).memLp_of_bilin (p := 2) 1
        (suContinuous_memLp_ball hp.continuous.continuousOn) hBI)
  · intro phi hp hpc hps
    exact suScalarEquations_vectorEquation hFI hBI heq hp hpc hps

end PoincareConjecture.M60
