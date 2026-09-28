import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Analysis.Calculus.Deriv.MeanValue









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace Poincare.Manifold
private theorem contMDiffAt_unique_time_root
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {F : ℝ × M → ℝ} {σ : M → ℝ} {I : Set ℝ} {V : Set M}
    (hI : IsOpen I) (hV : IsOpen V)
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (I ×ˢ V))
    (hroot : ∀ y ∈ V, σ y ∈ I ∧ F (σ y, y) = 0)
    (hinj : ∀ y ∈ V, InjOn (fun s => F (s, y)) I)
    {y : M} (hy : y ∈ V) {v : ℝ} (hv : v ≠ 0)
    (hder : HasDerivAt (fun s => F (s, y)) v (σ y)) :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ σ y := by
  let e := extChartAt (𝓡 n) y
  have he := (contMDiffWithinAt_extChartAt_symm_target (n := ∞) y
    (mem_extChartAt_target y)).contMDiffAt
      (extChartAt_target_mem_nhds' (I := 𝓡 n) (mem_extChartAt_target y))
  let G : EuclideanSpace ℝ (Fin n) × ℝ → ℝ := fun q => F (q.2, e.symm q.1)
  let q₀ : EuclideanSpace ℝ (Fin n) × ℝ := (e y, σ y)
  have hG : ContDiffAt ℝ ∞ G q₀ := by
    have he' : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ) (𝓡 n) ∞
        (fun q => e.symm q.1) q₀ := he.comp q₀ contDiffAt_fst.contMDiffAt
    have hpair : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ)
        (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞ (fun q => (q.2, e.symm q.1)) q₀ :=
      contDiffAt_snd.contMDiffAt.prodMk he'
    have hF' := hF.contMDiffAt ((hI.prod hV).mem_nhds
      (show (σ y, y) ∈ I ×ˢ V from ⟨(hroot y hy).1, hy⟩))
    have hsame : (q₀.2, e.symm q₀.1) = (σ y, y) := by
      simp only [q₀, e.left_inv (mem_extChartAt_source y)]
    rw [← hsame] at hF'
    exact (hF'.comp q₀ hpair).contDiffAt
  have hGder : HasDerivAt (fun s => G (q₀.1, s)) v (σ y) := by
    simpa only [G, q₀, e.left_inv (mem_extChartAt_source y)] using hder
  have hpart : (fderiv ℝ G q₀).comp
      (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) ℝ) =
      v • (ContinuousLinearMap.id ℝ ℝ) := by
    have hd := (hG.differentiableAt (by simp)).hasFDerivAt
    have hcomp := hd.comp (σ y)
      ((hasFDerivAt_const q₀.1 (σ y)).prodMk (hasFDerivAt_id (σ y)))
    have heq := hcomp.unique hGder.hasFDerivAt
    apply ContinuousLinearMap.ext
    intro z
    have hz := congrArg (fun L : ℝ →L[ℝ] ℝ => L z) heq
    change fderiv ℝ G q₀ (0, z) = z * v at hz
    change fderiv ℝ G q₀ (0, z) = v * z
    simpa only [mul_comm] using hz
  have hinv : ((fderiv ℝ G q₀).comp
      (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) ℝ)).IsInvertible := by
    rw [hpart]
    refine ⟨(LinearEquiv.smulOfNeZero ℝ ℝ v hv).toContinuousLinearEquiv, ?_⟩
    apply ContinuousLinearMap.ext
    intro z
    rfl
  let ψ := hG.implicitFunction (by simp) hinv
  have hψ : ContDiffAt ℝ ∞ ψ (e y) := hG.contDiffAt_implicitFunction (by simp) hinv
  have hψzero : ψ (e y) = σ y := hG.implicitFunction_apply_self (by simp) hinv
  have hψeq : ∀ᶠ z in 𝓝 (e y), G (z, ψ z) = G q₀ :=
    hG.eventually_apply_implicitFunction (by simp) hinv
  have hψI : ∀ᶠ z in 𝓝 (e y), ψ z ∈ I := by
    apply hψ.continuousAt.preimage_mem_nhds
    rw [hψzero]
    exact hI.mem_nhds (hroot y hy).1
  have hechart : ContMDiffAt (𝓡 n) (𝓡 n) ∞ e y := contMDiffAt_extChartAt
  have hcomp : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun z => ψ (e z)) y :=
    hψ.contMDiffAt.comp y hechart
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [hechart.continuousAt hψeq, hechart.continuousAt hψI,
    hV.mem_nhds hy, extChartAt_source_mem_nhds' (I := 𝓡 n) (mem_extChartAt_source y)] with z heq hIz hz hchartz
  apply (hinj z hz) (hroot z hz).1 hIz
  change F (σ z, z) = F (ψ (e z), z)
  rw [(hroot z hz).2]
  have hback : e.symm (e z) = z := e.left_inv hchartz
  change 0 = F (ψ (e z), z)
  conv_rhs => arg 1; arg 2; rw [← hback]
  change 0 = G (e z, ψ (e z))
  rw [heq]
  simpa only [G, q₀, e.left_inv (mem_extChartAt_source y)] using (hroot y hy).2.symm
end Poincare.Manifold


namespace Poincare.Manifold
private theorem time_control_of_derivative_le_neg
    {F : ℝ → ℝ} {F' : ℝ → ℝ} {a b c s : ℝ}
    (ha : a < 0) (hb : 0 < b) (hc : 0 < c) (hs : s ∈ Ioo a b)
    (hF : ∀ t ∈ Ioo a b, HasDerivAt F (F' t) t)
    (hd : ∀ t ∈ Ioo a b, F' t ≤ -c) :
    |s| ≤ |F 0 - F s| / c ∧ (0 ≤ s ↔ F s ≤ F 0) := by
  have hz : (0 : ℝ) ∈ Ioo a b := ⟨ha, hb⟩
  have hcont : ContinuousOn F (Ioo a b) := fun t ht =>
    (hF t ht).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ F (interior (Ioo a b)) := by
    simpa only [interior_Ioo] using
      (show DifferentiableOn ℝ F (Ioo a b) from fun t ht =>
        (hF t ht).differentiableAt.differentiableWithinAt)
  have hder : ∀ t ∈ interior (Ioo a b), deriv F t ≤ -c := by
    simpa only [interior_Ioo] using
      (show ∀ t ∈ Ioo a b, deriv F t ≤ -c from fun t ht => by
        rw [(hF t ht).deriv]; exact hd t ht)
  by_cases hpos : 0 ≤ s
  · have hle := (convex_Ioo a b).image_sub_le_mul_sub_of_deriv_le
      hcont hdiff hder 0 hz s hs hpos
    have hval : F s ≤ F 0 := by nlinarith
    refine ⟨?_, iff_of_true hpos hval⟩
    rw [abs_of_nonneg hpos, abs_of_nonneg (sub_nonneg.mpr hval)]
    exact (le_div_iff₀ hc).mpr (by nlinarith)
  · have hneg : s < 0 := lt_of_not_ge hpos
    have hle := (convex_Ioo a b).image_sub_le_mul_sub_of_deriv_le
      hcont hdiff hder s hs 0 hz hneg.le
    have hval : F 0 < F s := by nlinarith
    refine ⟨?_, iff_of_false hpos (not_le.mpr hval)⟩
    rw [abs_of_neg hneg, abs_of_neg (sub_neg.mpr hval)]
    exact (le_div_iff₀ hc).mpr (by nlinarith)
end Poincare.Manifold


namespace Poincare.Manifold
private theorem image_sub_le_of_derivative_le
    {F F' : ℝ → ℝ} {a b c u v : ℝ}
    (hF : ∀ s ∈ Ioo a b, HasDerivAt F (F' s) s)
    (hd : ∀ s ∈ Ioo a b, F' s ≤ -c)
    (hu : u ∈ Ioo a b) (hv : v ∈ Ioo a b) (huv : u ≤ v) :
    F v - F u ≤ -c * (v - u) :=
  (convex_Ioo a b).image_sub_le_mul_sub_of_deriv_le
    (fun s hs => (hF s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hF s (interior_subset hs)).differentiableAt.differentiableWithinAt)
    (fun s hs => by rw [(hF s (interior_subset hs)).deriv]; exact hd s (interior_subset hs))
    u hu v hv huv

private theorem strictAntiOn_of_derivative_le_neg
    {F F' : ℝ → ℝ} {a b c : ℝ} (hc : 0 < c)
    (hF : ∀ s ∈ Ioo a b, HasDerivAt F (F' s) s)
    (hd : ∀ s ∈ Ioo a b, F' s ≤ -c) : StrictAntiOn F (Ioo a b) := by
  intro u hu v hv huv
  have hle := image_sub_le_of_derivative_le hF hd hu hv huv.le
  have hneg : -c * (v - u) < 0 := mul_neg_of_neg_of_pos (by linarith) (sub_pos.mpr huv)
  linarith
end Poincare.Manifold


namespace Poincare.Manifold
theorem exists_smooth_hitting_time_of_derivative_le_neg
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {F : ℝ × M → ℝ} {F' : ℝ × M → ℝ} {W : Set M} (hW : IsOpen W)
    {T δ c : ℝ} (hT : 0 ≤ T) (hδ : 0 < δ) (hc : 0 < c)
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F
      (Ioo (-δ) (T + δ) ×ˢ W))
    (hder : ∀ y ∈ W, ∀ s ∈ Ioo (-δ) (T + δ), HasDerivAt (fun u => F (u, y)) (F' (s, y)) s)
    (hbound : ∀ y ∈ W, ∀ s ∈ Ioo (-δ) (T + δ), F' (s, y) ≤ -c)
    (t : ℝ) :
    ∃ (V : Set M) (σ : M → ℝ), IsOpen V ∧ V ⊆ W ∧
      {y | y ∈ W ∧ t ≤ F (0, y) ∧ F (0, y) ≤ t + c * T} ⊆ V ∧
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ σ V ∧
      (∀ y ∈ V, σ y ∈ Ioo (-δ) (T + δ) ∧ F (σ y, y) = t ∧
        |σ y| ≤ |F (0, y) - t| / c ∧ (0 ≤ σ y ↔ t ≤ F (0, y)) ∧
        (F (0, y) = t → σ y = 0)) ∧
      ∀ y ∈ V, t ≤ F (0, y) → F (0, y) ≤ t + c * T → σ y ∈ Icc 0 T := by
  classical
  let a := -δ / 2
  let b := T + δ / 2
  have ha : a ∈ Ioo (-δ) (T + δ) := by constructor <;> dsimp [a] <;> linarith
  have hb : b ∈ Ioo (-δ) (T + δ) := by constructor <;> dsimp [b] <;> linarith
  have hab : a ≤ b := by dsimp [a,b]; linarith
  have hzero : (0 : ℝ) ∈ Ioo (-δ) (T + δ) := by constructor <;> linarith
  have hIcc : Icc a b ⊆ Ioo (-δ) (T + δ) := fun _ hu =>
    ⟨ha.1.trans_le hu.1, hu.2.trans_lt hb.2⟩
  have hFtime (s : ℝ) (hs : s ∈ Ioo (-δ) (T + δ)) :
      ContinuousOn (fun y => F (s, y)) W := by
    intro y hy
    exact ((hF.contMDiffAt ((isOpen_Ioo.prod hW).mem_nhds ⟨hs, hy⟩)).comp y
      (contMDiffAt_const.prodMk contMDiffAt_id)).continuousAt.continuousWithinAt
  let V := W ∩ {y | t < F (a, y)} ∩ {y | F (b, y) < t}
  have hVo : IsOpen V := by
    have haopen := (hFtime a ha).isOpen_inter_preimage hW (isOpen_Ioi (a := t))
    have hbopen := (hFtime b hb).isOpen_inter_preimage hW (isOpen_Iio (a := t))
    convert haopen.inter hbopen using 1
    ext y
    simp only [V, mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_Ioi, mem_Iio]
    tauto
  have hVW : V ⊆ W := fun _ hy => hy.1.1
  have hK : {y | y ∈ W ∧ t ≤ F (0, y) ∧ F (0, y) ≤ t + c * T} ⊆ V := by
    intro y hy
    have hleft := Poincare.Manifold.image_sub_le_of_derivative_le
      (hder y hy.1) (hbound y hy.1) ha hzero (by dsimp [a]; linarith)
    have hright := Poincare.Manifold.image_sub_le_of_derivative_le
      (hder y hy.1) (hbound y hy.1) hzero hb (by dsimp [b]; linarith)
    refine ⟨⟨hy.1, ?_⟩, ?_⟩
    · change t < F (a,y)
      have hpos : 0 < c * (0-a) := mul_pos hc (by dsimp[a]; linarith)
      nlinarith [hy.2.1]
    · change F (b,y) < t
      have hpos : 0 < c * (b-T) := mul_pos hc (by dsimp[b]; linarith)
      nlinarith [hy.2.2]
  have hex (y : M) : ∃ s : ℝ, y ∈ V → s ∈ Ioo (-δ) (T + δ) ∧ F (s, y) = t := by
    by_cases hy : y ∈ V
    · obtain ⟨s, hs, heq⟩ := intermediate_value_Icc' hab
        (show ContinuousOn (fun s => F (s,y)) (Icc a b) from fun s hs =>
          (hder y (hVW hy) s (hIcc hs)).continuousAt.continuousWithinAt)
        ⟨hy.2.le, hy.1.2.le⟩
      exact ⟨s, fun _ => ⟨hIcc hs, heq⟩⟩
    · exact ⟨0, fun h => (hy h).elim⟩
  choose σ hσroot using hex
  have hanti (y : M) (hy : y ∈ W) : StrictAntiOn (fun s => F (s,y)) (Ioo (-δ) (T + δ)) :=
    Poincare.Manifold.strictAntiOn_of_derivative_le_neg hc (hder y hy) (hbound y hy)
  have hσsmooth : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ σ V := by
    intro y hy
    apply (contMDiffAt_unique_time_root isOpen_Ioo hVo
      ((hF.mono (prod_mono_right hVW)).sub contMDiffOn_const)
      (F := fun q => F q - t) (v := F' (σ y,y)) ?_ ?_ hy ?_ ?_).contMDiffWithinAt
    · intro z hz
      exact ⟨(hσroot z hz).1, sub_eq_zero.mpr (hσroot z hz).2⟩
    · intro z hz s hs u hu heq
      apply (hanti z (hVW hz)).injOn hs hu
      exact sub_left_injective heq
    · exact (lt_of_le_of_lt (hbound y (hVW hy) _ (hσroot y hy).1) (by linarith : -c < 0)).ne
    · exact (hder y (hVW hy) _ (hσroot y hy).1).sub_const t
  have hcontrol (y : M) (hy : y ∈ V) :
      |σ y| ≤ |F (0,y)-t| / c ∧ (0 ≤ σ y ↔ t ≤ F (0,y)) := by
    have hd := Poincare.Manifold.time_control_of_derivative_le_neg
      (by linarith : -δ < 0) (by linarith : 0 < T+δ) hc (hσroot y hy).1
      (hder y (hVW hy)) (hbound y (hVW hy))
    simpa only [(hσroot y hy).2] using hd
  refine ⟨V, σ, hVo, hVW, hK, hσsmooth, ?_, ?_⟩
  · intro y hy
    refine ⟨(hσroot y hy).1, (hσroot y hy).2, (hcontrol y hy).1, (hcontrol y hy).2, ?_⟩
    intro heq
    apply abs_eq_zero.mp
    apply le_antisymm _ (abs_nonneg _)
    simpa only [heq, sub_self, abs_zero, zero_div] using (hcontrol y hy).1
  · intro y hy hlow hupp
    have hs0 := (hcontrol y hy).2.mpr hlow
    refine ⟨hs0, ?_⟩
    have hle : σ y ≤ (F (0,y)-t)/c := by
      simpa only [abs_of_nonneg hs0, abs_of_nonneg (sub_nonneg.mpr hlow)] using (hcontrol y hy).1
    exact hle.trans ((div_le_iff₀ hc).mpr (by linarith))
end Poincare.Manifold
