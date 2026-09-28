




import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Topology.Order.LiminfLimsup









open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal

noncomputable section

namespace Poincare.Analysis.Sobolev.WeakCompactness


def WeakConverges {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : ℕ → F) (v : F) : Prop :=
  ∀ L : StrongDual ℝ F, Tendsto (fun n => L (u n)) atTop (𝓝 (L v))

section Hilbert

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

private theorem weakConverges_iff_inner {u : ℕ → F} {v : F} :
    WeakConverges u v ↔ ∀ z : F,
      Tendsto (fun n => inner ℝ (u n) z) atTop (𝓝 (inner ℝ v z)) := by
  constructor
  · intro hu z
    simpa only [InnerProductSpace.toDual_apply_apply, real_inner_comm] using
      hu ((InnerProductSpace.toDual ℝ F) z)
  · intro hu A
    let z := (InnerProductSpace.toDual ℝ F).symm A
    simpa only [← InnerProductSpace.toDual_symm_apply, real_inner_comm] using hu z



private theorem extract_hilbert (u : ℕ → F) (hu : Bornology.IsBounded (range u)) :
    ∃ v : F, ∃ k : ℕ → ℕ, StrictMono k ∧ WeakConverges (fun n => u (k n)) v := by
  let S : Submodule ℝ F := (Submodule.span ℝ (range u)).topologicalClosure
  have huS (n : ℕ) : u n ∈ S :=
    subset_closure (Submodule.subset_span ⟨n, rfl⟩)
  let uS : ℕ → S := fun n => ⟨u n, huS n⟩
  letI : IsClosed (S : Set F) := Submodule.isClosed_topologicalClosure _
  letI : CompleteSpace S := IsClosed.completeSpace_coe
  have hsep : TopologicalSpace.IsSeparable (S : Set F) := by
    rw [show (S : Set F) = closure (Submodule.span ℝ (range u) : Set F) from
      Submodule.topologicalClosure_coe _]
    exact (Set.countable_range u).isSeparable.span.closure
  letI : TopologicalSpace.SeparableSpace S := hsep.separableSpace
  have hb : Bornology.IsBounded (range uS) := by
    rw [Metric.isBounded_range_iff] at hu ⊢
    obtain ⟨B, hB⟩ := hu
    exact ⟨B, fun i j => hB i j⟩
  obtain ⟨B, hB⟩ := (Metric.isBounded_iff_subset_closedBall (0 : S)).mp hb
  let a : ℕ → WeakDual ℝ S := fun n =>
    StrongDual.toWeakDual ((InnerProductSpace.toDual ℝ S) (uS n))
  have ha : ∀ n, a n ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 B := by
    intro n
    change dist ((InnerProductSpace.toDual ℝ S) (uS n)) 0 ≤ B
    simpa only [LinearIsometryEquiv.norm_map, Metric.mem_closedBall, dist_zero_right]
      using hB ⟨n, rfl⟩
  obtain ⟨L, -, k, hk, hlim⟩ := (WeakDual.isSeqCompact_closedBall ℝ S 0 B) ha
  let v : S := (InnerProductSpace.toDual ℝ S).symm (WeakDual.toStrongDual L)
  have hv (z : S) : Tendsto (fun n => inner ℝ (uS (k n)) z) atTop
      (𝓝 (inner ℝ v z)) := by
    have hz := tendsto_iff_forall_eval_tendsto_topDualPairing.mp hlim z
    change Tendsto (fun n => ((InnerProductSpace.toDual ℝ S) (uS (k n))) z)
      atTop (𝓝 ((WeakDual.toStrongDual L) z)) at hz
    simpa only [InnerProductSpace.toDual_apply_apply, v,
      InnerProductSpace.toDual_symm_apply] using hz
  refine ⟨v, k, hk, fun A => ?_⟩
  have hw := weakConverges_iff_inner.mpr hv (A.comp S.subtypeL)
  simpa only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, uS] using hw



theorem norm_sq_le_liminf {u : ℕ → F} {v : F} (hw : WeakConverges u v)
    {B : ℝ} (hB : ∀ n, ‖u n‖ ^ 2 ≤ B) :
    ‖v‖ ^ 2 ≤ liminf (fun n => ‖u n‖ ^ 2) atTop := by
  have ht := (hw ((InnerProductSpace.toDual ℝ F) v)).const_mul 2
  have ht' : Tendsto (fun n => 2 * inner ℝ v (u n) - ‖v‖ ^ 2) atTop
      (𝓝 (‖v‖ ^ 2)) := by
    have heq : 2 * ((InnerProductSpace.toDual ℝ F) v) v - ‖v‖ ^ 2 = ‖v‖ ^ 2 := by
      rw [InnerProductSpace.toDual_apply_apply, real_inner_self_eq_norm_sq]
      ring
    have hh := ht.sub_const (‖v‖ ^ 2)
    rw [heq] at hh
    exact hh
  have hle : ∀ n, 2 * inner ℝ v (u n) - ‖v‖ ^ 2 ≤ ‖u n‖ ^ 2 := by
    intro n
    have h := sq_nonneg ‖v - u n‖
    rw [norm_sub_sq_real] at h
    linarith
  rw [← ht'.liminf_eq]
  exact liminf_le_liminf (Eventually.of_forall hle) ht'.isBoundedUnder_ge
    ((isBoundedUnder_of_eventually_le (Eventually.of_forall hB)).isCoboundedUnder_ge)

end Hilbert

section Pairing

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]



def testIntegral (phi : X → ℝ) (hphi : MemLp phi 2 μ) : Lp F 2 μ →L[ℝ] F :=
  (ContinuousLinearMap.lsmul ℝ ℝ).lpPairing μ 2 2 (hphi.toLp phi)


theorem testIntegral_apply (phi : X → ℝ) (hphi : MemLp phi 2 μ) (u : Lp F 2 μ) :
    testIntegral phi hphi u = ∫ x, phi x • u x ∂μ := by
  rw [testIntegral, ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [hphi.coeFn_toLp] with x hx
  simp only [ContinuousLinearMap.lsmul_apply, hx]



theorem testIntegral_toLp (phi : X → ℝ) (hphi : MemLp phi 2 μ)
    (u : X → F) (hu : MemLp u 2 μ) :
    testIntegral phi hphi (hu.toLp u) = ∫ x, phi x • u x ∂μ := by
  rw [testIntegral_apply]
  exact integral_congr_ae (hu.coeFn_toLp.mono fun x hx =>
    congrArg (fun v => phi x • v) hx)



theorem weak_limit_linear_identity {u v : ℕ → Lp F 2 μ} {u0 v0 : Lp F 2 μ}
    (hu : WeakConverges u u0) (hv : WeakConverges v v0)
    (A B : Lp F 2 μ →L[ℝ] F) (hid : ∀ n, A (v n) = -B (u n)) :
    A v0 = -B u0 := by
  apply ext_inner_left ℝ
  intro z
  let L := (InnerProductSpace.toDual ℝ F) z
  have ha := hv (L.comp A)
  have hb := (hu (L.comp B)).neg
  have heq : (fun n => L (A (v n))) = (fun n => -L (B (u n))) := by
    funext n; rw [hid, map_neg]
  change Tendsto (fun n => L (A (v n))) atTop (𝓝 (L (A v0))) at ha
  rw [heq] at ha
  have hh := tendsto_nhds_unique ha hb
  simpa only [L, ContinuousLinearMap.comp_apply, InnerProductSpace.toDual_apply_apply,
    inner_neg_right] using hh

end Pairing

variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D]
  [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in


theorem integrable_test_smul {s : Set D} (hs : IsOpen s)
    {phi : D → ℝ} (hphi : Continuous phi) (hc : HasCompactSupport phi)
    (hsub : tsupport phi ⊆ s) {u : D → E} (hu : ContinuousOn u s) :
    Integrable (fun x => phi x • u x) := by
  have hcont : Continuous (fun x => phi x • u x) :=
    (hphi.continuousOn.smul hu).continuous_of_tsupport_subset hs
      ((tsupport_smul_subset_left phi u).trans hsub)
  exact hcont.integrable_of_hasCompactSupport hc.smul_right

omit [CompleteSpace E] in


theorem integral_test_fderiv {s : Set D} (hs : IsOpen s) {u : D → E}
    (hu : ContDiffOn ℝ 1 u s) {phi : D → ℝ} (hphi : ContDiff ℝ ∞ phi)
    (hc : HasCompactSupport phi) (hsub : tsupport phi ⊆ s) (v : D) :
    (∫ x, phi x • fderiv ℝ u x v) = -(∫ x, fderiv ℝ phi x v • u x) := by
  have hdu : ContinuousOn (fun x => fderiv ℝ u x v) s :=
    (hu.continuousOn_fderiv_of_isOpen hs le_rfl).clm_apply continuousOn_const
  have hdphi : Continuous (fun x => fderiv ℝ phi x v) :=
    (hphi.continuous_fderiv (by norm_num)).clm_apply continuous_const
  apply integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
  · exact integrable_test_smul hs hdphi (hc.fderiv_apply ℝ v)
      ((tsupport_fderiv_apply_subset ℝ v).trans hsub) hu.continuousOn
  · exact integrable_test_smul hs hphi.continuous hc hsub hdu
  · exact integrable_test_smul hs hphi.continuous hc hsub hu.continuousOn
  · intro x _
    exact hphi.differentiable (by norm_num) x
  · intro x hx
    exact (hu.contDiffAt (hs.mem_nhds (hsub hx))).differentiableAt (by norm_num)

omit [CompleteSpace E] in


theorem setIntegral_test_fderiv {s : Set D} (hs : IsOpen s) {u : D → E}
    (hu : ContDiffOn ℝ 1 u s) {phi : D → ℝ} (hphi : ContDiff ℝ ∞ phi)
    (hc : HasCompactSupport phi) (hsub : tsupport phi ⊆ s) (v : D) :
    (∫ x in s, phi x • fderiv ℝ u x v) = -(∫ x in s, fderiv ℝ phi x v • u x) := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hsub ht)), zero_smul])]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport
      (fun ht => hx (hsub (tsupport_fderiv_apply_subset ℝ v ht))), zero_smul])]
  exact integral_test_fderiv hs hu hphi hc hsub v



theorem distributional_identity_of_weak_limits {s : Set D} (hs : IsOpen s)
    (f : ℕ → D → E) (hf : ∀ n, ContDiffOn ℝ 1 (f n) s) (v : D)
    (hU : ∀ n, MemLp (f n) 2 (volume.restrict s))
    (hV : ∀ n, MemLp (fun x => fderiv ℝ (f n) x v) 2 (volume.restrict s))
    {u V : Lp E 2 (volume.restrict s)}
    (hu : WeakConverges (fun n => (hU n).toLp (f n)) u)
    (hv : WeakConverges (fun n => (hV n).toLp (fun x => fderiv ℝ (f n) x v)) V)
    {phi : D → ℝ} (hphi : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (hsub : tsupport phi ⊆ s) :
    (∫ x in s, phi x • V x) = -(∫ x in s, fderiv ℝ phi x v • u x) := by
  have hphi2 : MemLp phi 2 (volume.restrict s) :=
    hphi.continuous.memLp_of_hasCompactSupport hc
  have hdphi2 : MemLp (fun x => fderiv ℝ phi x v) 2 (volume.restrict s) :=
    ((hphi.continuous_fderiv (by norm_num)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ v)
  have hh := weak_limit_linear_identity hu hv
    (testIntegral phi hphi2) (testIntegral (fun x => fderiv ℝ phi x v) hdphi2)
    (fun n => by
      rw [testIntegral_toLp, testIntegral_toLp]
      exact setIntegral_test_fderiv hs (hf n) hphi hc hsub v)
  simpa only [testIntegral_apply] using hh




theorem weak_w12_subsequence {s : Set D} (hs : IsOpen s)
    (f : ℕ → D → E) (hf : ∀ n, ContDiffOn ℝ 1 (f n) s)
    {ι : Type*} [Fintype ι] (b : ι → D)
    (hU : ∀ n, MemLp (f n) 2 (volume.restrict s))
    (hV : ∀ n i, MemLp (fun x => fderiv ℝ (f n) x (b i)) 2 (volume.restrict s))
    {A B : ℝ} (hA : ∀ n, ‖(hU n).toLp (f n)‖ ≤ A)
    (hB : ∀ n, (∑ i, ‖(hV n i).toLp (fun x => fderiv ℝ (f n) x (b i))‖ ^ 2) ≤ B) :
    ∃ u : Lp E 2 (volume.restrict s), ∃ V : ι → Lp E 2 (volume.restrict s),
      ∃ k : ℕ → ℕ, StrictMono k ∧
        WeakConverges (fun n => (hU (k n)).toLp (f (k n))) u ∧
        (∀ i, WeakConverges
          (fun n => (hV (k n) i).toLp (fun x => fderiv ℝ (f (k n)) x (b i))) (V i)) ∧
        (∀ i (phi : D → ℝ), ContDiff ℝ ∞ phi → HasCompactSupport phi → tsupport phi ⊆ s →
          (∫ x in s, phi x • V i x) = -(∫ x in s, fderiv ℝ phi x (b i) • u x)) ∧
        (∑ i, ‖V i‖ ^ 2) ≤ liminf
          (fun n => ∑ i, ‖(hV (k n) i).toLp (fun x => fderiv ℝ (f (k n)) x (b i))‖ ^ 2) atTop ∧
        (∑ i, ‖V i‖ ^ 2) ≤ B := by
  let U := fun n => (hU n).toLp (f n)
  have hUb : Bornology.IsBounded (range U) :=
    (Metric.isBounded_iff_subset_closedBall (0 : Lp E 2 (volume.restrict s))).mpr
      ⟨A, by rintro _ ⟨n, rfl⟩; simpa only [Metric.mem_closedBall, dist_zero_right] using hA n⟩
  obtain ⟨u, k0, hk0, hu⟩ := extract_hilbert U hUb
  let W : ℕ → PiLp 2 (fun _ : ι => Lp E 2 (volume.restrict s)) := fun n =>
    WithLp.toLp 2 (fun i => (hV (k0 n) i).toLp (fun x => fderiv ℝ (f (k0 n)) x (b i)))
  have hWsq : ∀ n, ‖W n‖ ^ 2 ≤ B := by
    intro n
    rw [PiLp.norm_sq_eq_of_L2]
    exact hB (k0 n)
  have hWb : Bornology.IsBounded (range W) :=
    (Metric.isBounded_iff_subset_closedBall (0 : PiLp 2 (fun _ : ι => Lp E 2 (volume.restrict s)))).mpr
      ⟨Real.sqrt B, by
        rintro _ ⟨n, rfl⟩
        simpa only [Metric.mem_closedBall, dist_zero_right] using Real.le_sqrt_of_sq_le (hWsq n)⟩
  obtain ⟨V, k1, hk1, hv⟩ := extract_hilbert W hWb
  have hu' : WeakConverges (fun n => U (k0 (k1 n))) u :=
    fun L => (hu L).comp hk1.tendsto_atTop
  have hv' (i : ι) : WeakConverges
      (fun n => (hV (k0 (k1 n)) i).toLp
        (fun x => fderiv ℝ (f (k0 (k1 n))) x (b i))) (V i) := by
    intro L
    exact hv (L.comp (PiLp.proj 2 (fun _ : ι => Lp E 2 (volume.restrict s)) i))
  have hls := norm_sq_le_liminf hv (fun n => hWsq (k1 n))
  simp only [PiLp.norm_sq_eq_of_L2] at hls
  refine ⟨u, fun i => V i, k0 ∘ k1, hk0.comp hk1, hu', hv', ?_, hls, ?_⟩
  · intro i phi hphi hc hsub
    exact distributional_identity_of_weak_limits hs (fun n => f (k0 (k1 n)))
      (fun n => hf _) (b i) (fun n => hU _) (fun n => hV _ i) hu' (hv' i) hphi hc hsub
  · apply hls.trans
    apply liminf_le_of_le (isBoundedUnder_of_eventually_ge
      (Eventually.of_forall (fun n => Finset.sum_nonneg (fun i _ => sq_nonneg _))))
    intro a ha
    obtain ⟨n, hn⟩ := ha.exists
    exact hn.trans (hB (k0 (k1 n)))

end Poincare.Analysis.Sobolev.WeakCompactness
