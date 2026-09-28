




import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.CanonicalEquation
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.WeakCompactness.DerivativeLimit
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.WeakCompactness.StrongLimit










open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Interior

open Poincare.Analysis.Sobolev.WeakCompactness
open Poincare.Analysis.Sobolev.WeakCompactness

section HilbertExtraction

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

private theorem weakConverges_iff_inner_spacetime {u : ℕ → F} {v : F} :
    WeakConverges u v ↔ ∀ z : F,
      Tendsto (fun n => inner ℝ (u n) z) atTop (𝓝 (inner ℝ v z)) := by
  constructor
  · intro hu z
    simpa only [InnerProductSpace.toDual_apply_apply, real_inner_comm] using
      hu ((InnerProductSpace.toDual ℝ F) z)
  · intro hu A
    let z := (InnerProductSpace.toDual ℝ F).symm A
    simpa only [← InnerProductSpace.toDual_symm_apply, real_inner_comm] using hu z

private theorem extract_hilbert_spacetime (u : ℕ → F) (hu : Bornology.IsBounded (range u)) :
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
  have hw := weakConverges_iff_inner_spacetime.mpr hv (A.comp S.subtypeL)
  simpa only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, uS] using hw

end HilbertExtraction

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [FiniteDimensional ℝ D] [MeasureSpace D] [BorelSpace D]
  [Measure.IsAddHaarMeasure (volume : Measure D)]


theorem setIntegral_test_fderiv_spacetime {s : Set D} (hs : IsOpen s) {u : D → ℝ}
    (hu : ContDiffOn ℝ 1 u s) {phi : D → ℝ} (hphi : ContDiff ℝ ∞ phi)
    (hc : HasCompactSupport phi) (hsub : tsupport phi ⊆ s) (v : D) :
    (∫ x in s, phi x • fderiv ℝ u x v) = -(∫ x in s, fderiv ℝ phi x v • u x) := by
  have hdu : ContinuousOn (fun x => fderiv ℝ u x v) s :=
    (hu.continuousOn_fderiv_of_isOpen hs le_rfl).clm_apply continuousOn_const
  have hdphi : Continuous (fun x => fderiv ℝ phi x v) :=
    (hphi.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hleft : Integrable (fun x => phi x • fderiv ℝ u x v) := by
    exact (hphi.continuous.continuousOn.smul hdu).continuous_of_tsupport_subset hs
      ((tsupport_smul_subset_left phi _).trans hsub) |>.integrable_of_hasCompactSupport hc.smul_right
  have hright : Integrable (fun x => fderiv ℝ phi x v • u x) := by
    exact (hdphi.continuousOn.smul hu.continuousOn).continuous_of_tsupport_subset hs
      ((tsupport_smul_subset_left _ u).trans ((tsupport_fderiv_apply_subset ℝ v).trans hsub))
      |>.integrable_of_hasCompactSupport (hc.fderiv_apply ℝ v).smul_right
  have hprod : Integrable (fun x => phi x • u x) := by
    exact (hphi.continuous.continuousOn.smul hu.continuousOn).continuous_of_tsupport_subset hs
      ((tsupport_smul_subset_left phi u).trans hsub) |>.integrable_of_hasCompactSupport hc.smul_right
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hsub ht)), zero_smul])]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport
      (fun ht => hx (hsub (tsupport_fderiv_apply_subset ℝ v ht))), zero_smul])]
  exact integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    hright hleft hprod
    (fun x _ => hphi.differentiable (by norm_num) x)
    (fun x hx => (hu.contDiffAt (hs.mem_nhds (hsub hx))).differentiableAt (by norm_num))


theorem distributional_identity_of_weak_limits_spacetime {s : Set D} (hs : IsOpen s)
    (f : ℕ → D → ℝ) (hf : ∀ n, ContDiffOn ℝ 1 (f n) s) (v : D)
    (hU : ∀ n, MemLp (f n) 2 (volume.restrict s))
    (hV : ∀ n, MemLp (fun x => fderiv ℝ (f n) x v) 2 (volume.restrict s))
    {u V : Lp ℝ 2 (volume.restrict s)}
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
      simpa only [smul_eq_mul] using
        setIntegral_test_fderiv_spacetime hs (hf n) hphi hc hsub v)
  simpa only [testIntegral_apply] using hh


theorem weak_w12_subsequence_spacetime {s : Set D} (hs : IsOpen s)
    (f : ℕ → D → ℝ) (hf : ∀ n, ContDiffOn ℝ 1 (f n) s)
    {ι : Type*} [Fintype ι] (b : ι → D)
    (hU : ∀ n, MemLp (f n) 2 (volume.restrict s))
    (hV : ∀ n i, MemLp (fun x => fderiv ℝ (f n) x (b i)) 2 (volume.restrict s))
    {A B : ℝ} (hA : ∀ n, ‖(hU n).toLp (f n)‖ ≤ A)
    (hB : ∀ n, (∑ i, ‖(hV n i).toLp (fun x => fderiv ℝ (f n) x (b i))‖ ^ 2) ≤ B) :
    ∃ u : Lp ℝ 2 (volume.restrict s), ∃ V : ι → Lp ℝ 2 (volume.restrict s),
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
    (Metric.isBounded_iff_subset_closedBall (0 : Lp ℝ 2 (volume.restrict s))).mpr
      ⟨A, by rintro _ ⟨n, rfl⟩; simpa only [Metric.mem_closedBall, dist_zero_right] using hA n⟩
  obtain ⟨u, k0, hk0, hu⟩ := extract_hilbert_spacetime U hUb
  let W : ℕ → PiLp 2 (fun _ : ι => Lp ℝ 2 (volume.restrict s)) := fun n =>
    WithLp.toLp 2 (fun i => (hV (k0 n) i).toLp
      (fun x => fderiv ℝ (f (k0 n)) x (b i)))
  have hWsq : ∀ n, ‖W n‖ ^ 2 ≤ B := by
    intro n
    rw [PiLp.norm_sq_eq_of_L2]
    exact hB (k0 n)
  have hWb : Bornology.IsBounded (range W) :=
    (Metric.isBounded_iff_subset_closedBall
      (0 : PiLp 2 (fun _ : ι => Lp ℝ 2 (volume.restrict s)))).mpr
      ⟨Real.sqrt B, by
        rintro _ ⟨n, rfl⟩
        simpa only [Metric.mem_closedBall, dist_zero_right] using
          Real.le_sqrt_of_sq_le (hWsq n)⟩
  obtain ⟨V, k1, hk1, hv⟩ := extract_hilbert_spacetime W hWb
  have hu' : WeakConverges (fun n => U (k0 (k1 n))) u :=
    fun L => (hu L).comp hk1.tendsto_atTop
  have hv' (i : ι) : WeakConverges
      (fun n => (hV (k0 (k1 n)) i).toLp
        (fun x => fderiv ℝ (f (k0 (k1 n))) x (b i))) (V i) := by
    intro L
    exact hv (L.comp (PiLp.proj 2 (fun _ : ι => Lp ℝ 2 (volume.restrict s)) i))
  have hls := norm_sq_le_liminf hv (fun n => hWsq (k1 n))
  simp only [PiLp.norm_sq_eq_of_L2] at hls
  refine ⟨u, fun i => V i, k0 ∘ k1, hk0.comp hk1, hu', hv', ?_, hls, ?_⟩
  · intro i phi hphi hc hsub
    exact distributional_identity_of_weak_limits_spacetime hs
      (fun n => f (k0 (k1 n))) (fun n => hf _) (b i)
      (fun n => hU _) (fun n => hV _ i) hu' (hv' i) hphi hc hsub
  · apply hls.trans
    apply liminf_le_of_le (isBoundedUnder_of_eventually_ge
      (Eventually.of_forall (fun n => Finset.sum_nonneg (fun i _ => sq_nonneg _))))
    intro a ha
    obtain ⟨n, hn⟩ := ha.exists
    exact hn.trans (hB (k0 (k1 n)))

variable {n : ℕ}

local instance : Measure.IsAddHaarMeasure (volume : Measure (Spacetime n)) := by
  change ((volume : Measure (Euclid n)).prod (volume : Measure ℝ)).IsAddHaarMeasure
  infer_instance


theorem weak_derivatives_of_uniform_limit
    {s : Set (Spacetime n)} (hs : IsOpen s) [IsFiniteMeasure (volume.restrict s)]
    {f : Spacetime n → ℝ} (hf : MemLp f 2 (volume.restrict s))
    (u : ℕ → Spacetime n → ℝ) (hu : ∀ m, ContDiffOn ℝ 1 (u m) s)
    {ι : Type*} [Fintype ι] (b : ι → Spacetime n)
    (hU : ∀ m, MemLp (u m) 2 (volume.restrict s))
    (hV : ∀ m i, MemLp
      (fun z => fderiv ℝ (u m) z (b i)) 2 (volume.restrict s))
    (hlim : TendstoUniformlyOn u f atTop s)
    {B : ℝ} (hB : ∀ m, (∑ i, ‖(hV m i).toLp
      (fun z => fderiv ℝ (u m) z (b i))‖ ^ 2) ≤ B) :
    ∃ V : ι → Lp ℝ 2 (volume.restrict s), ∃ k : ℕ → ℕ, StrictMono k ∧
      (∀ i, WeakConverges
        (fun m => (hV (k m) i).toLp
          (fun z => fderiv ℝ (u (k m)) z (b i))) (V i)) ∧
      (∀ i (phi : Spacetime n → ℝ), ContDiff ℝ ∞ phi → HasCompactSupport phi →
        tsupport phi ⊆ s →
        (∫ z in s, phi z • V i z) =
          -(∫ z in s, fderiv ℝ phi z (b i) • f z)) ∧
      (∑ i, ‖V i‖ ^ 2) ≤ B := by
  have hstrong := tendsto_toLp_of_uniformlyOn hs.measurableSet hU hf hlim
  obtain ⟨A, hA⟩ :=
    (Metric.isBounded_range_of_tendsto _ hstrong).exists_norm_le
  obtain ⟨u₀, V, k, hk, hu₀, hVv, hdist, _, henergy⟩ :=
    weak_w12_subsequence_spacetime hs u hu b hU hV
      (fun m => hA _ (mem_range_self m)) hB
  have hu₀f : u₀ = hf.toLp f :=
    eq_of_strong_and_weak_limit (hstrong.comp hk.tendsto_atTop) hu₀
  refine ⟨V, k, hk, hVv, ?_, henergy⟩
  intro i phi hphi hc hsub
  rw [hdist i phi hphi hc hsub, hu₀f]
  congr 1
  exact integral_congr_ae (hf.coeFn_toLp.mono fun z hz =>
    congrArg (fun y => fderiv ℝ phi z (b i) • y) hz)

end Poincare.Analysis.Parabolic.WeakRegularity.Interior
