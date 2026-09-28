import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.Equicontinuity
import PoincareConjecture.Proofs.M07.Topology.Sequences.Diagonal

set_option autoImplicit false

open Filter Set
open Metric
open scoped ContDiff Topology

namespace Poincare.Analysis.Calculus

theorem limit_hasFDerivAt_of_tendstoLocallyUniformlyOn
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {s : Set X} {f : ℕ → X → Y} {g : X → Y}
    {f' : ℕ → X → X →L[ℝ] Y} {g' : X → X →L[ℝ] Y}
    (hs : IsOpen s)
    (hf' : TendstoLocallyUniformlyOn f' g' atTop s)
    (hf : ∀ n x, x ∈ s → HasFDerivAt (f n) (f' n x) x)
    (hfg : ∀ x, x ∈ s → Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) :
    ∀ x, x ∈ s → HasFDerivAt g (g' x) x := by
  intro x hx
  exact hasFDerivAt_of_tendstoLocallyUniformlyOn
    (l := atTop) (f := f) (g := g) (f' := f') (g' := g') hs hf' hf hfg hx

variable {d : ℕ} {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def LocallyEventuallyBoundedDerivatives (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (f : ℕ → EuclideanSpace ℝ (Fin d) → E) : Prop :=
  ∀ K : Set (EuclideanSpace ℝ (Fin d)), IsCompact K → K ⊆ Ω →
    ∀ m : ℕ, ∃ B : ℝ, ∀ᶠ j : ℕ in atTop,
      ∀ x ∈ K, ‖iteratedFDeriv ℝ m (f j) x‖ ≤ B

theorem norm_iteratedFDeriv_le_on_compact
    {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : IsOpen Ω) (f : ℕ → EuclideanSpace ℝ (Fin d) → E)
    (hf : ∀ j, ContDiffOn ℝ ∞ (f j) Ω)
    (hbound : LocallyEventuallyBoundedDerivatives Ω f)
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (m : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ j x, x ∈ K →
      ‖iteratedFDeriv ℝ m (f j) x‖ ≤ B := by
  classical
  have hc (j : ℕ) : ContinuousOn (iteratedFDeriv ℝ m (f j)) K := by
    intro x hx
    exact ((hf j x (hKΩ hx)).contDiffAt (hΩ.mem_nhds (hKΩ hx))).continuousAt_iteratedFDeriv
      (by exact_mod_cast (show (m : ℕ∞) ≤ ⊤ from le_top)) |>.continuousWithinAt
  choose b hb using fun j => hK.exists_bound_of_continuousOn (hc j)
  obtain ⟨B, hB⟩ := hbound K hK hKΩ m
  obtain ⟨N, hN⟩ := eventually_atTop.1 hB
  let C := ∑ j ∈ Finset.range N, max (b j) 0
  have hC : 0 ≤ C := Finset.sum_nonneg fun j _ => le_max_right _ _
  refine ⟨max B 0 + C, add_nonneg (le_max_right _ _) hC, ?_⟩
  intro j x hx
  by_cases hj : N ≤ j
  · exact (hN j hj x hx).trans ((le_max_left _ _).trans (le_add_of_nonneg_right hC))
  · have hbj : max (b j) 0 ≤ C :=
      Finset.single_le_sum (fun i _ => le_max_right (b i) 0)
        (Finset.mem_range.mpr (Nat.lt_of_not_ge hj))
    exact (hb j x hx).trans ((le_max_left _ _).trans
      (hbj.trans (le_add_of_nonneg_left (le_max_right _ _))))

private theorem equicontinuous_iteratedFDeriv
    {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : IsOpen Ω) (f : ℕ → EuclideanSpace ℝ (Fin d) → E)
    (hf : ∀ j, ContDiffOn ℝ ∞ (f j) Ω)
    (hbound : LocallyEventuallyBoundedDerivatives Ω f) (m : ℕ) :
    Equicontinuous (fun j (x : Ω) => iteratedFDeriv ℝ m (f j) x) := by
  intro x
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hΩ x x.property
  obtain ⟨C, hC, hCbound⟩ := norm_iteratedFDeriv_le_on_compact hΩ f hf hbound
    (isCompact_closedBall (x : EuclideanSpace ℝ (Fin d)) (r / 2))
    ((closedBall_subset_ball (half_lt_self hr)).trans hball) (m + 1)
  have hLip (j : ℕ) (y : EuclideanSpace ℝ (Fin d)) (hy : y ∈ closedBall (x : EuclideanSpace ℝ (Fin d)) (r / 2)) :
      ‖iteratedFDeriv ℝ m (f j) (x : EuclideanSpace ℝ (Fin d)) -
        iteratedFDeriv ℝ m (f j) y‖ ≤ C * ‖(x : EuclideanSpace ℝ (Fin d)) - y‖ := by
    apply (convex_closedBall (x : EuclideanSpace ℝ (Fin d)) (r / 2)).norm_image_sub_le_of_norm_fderiv_le
      (𝕜 := ℝ) (fun z hz => ?_) (fun z hz => ?_) hy (mem_closedBall_self (le_of_lt (half_pos hr)))
    · exact ((hf j z (hball ((closedBall_subset_ball (half_lt_self hr)) hz))).contDiffAt
        (hΩ.mem_nhds (hball ((closedBall_subset_ball (half_lt_self hr)) hz)))).differentiableAt_iteratedFDeriv
        (ENat.natCast_lt_of_coe_top_le_withTop (N := (∞ : ℕ∞ω)) le_rfl m)
    · rw [norm_fderiv_iteratedFDeriv]
      exact hCbound j z hz
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  refine ⟨min (r / 2) (ε / (C + 1)), lt_min (half_pos hr) (div_pos hε (by linarith)), ?_⟩
  intro y hy j
  have hyr : (y : EuclideanSpace ℝ (Fin d)) ∈ closedBall (x : EuclideanSpace ℝ (Fin d)) (r / 2) :=
    (lt_of_lt_of_le hy (min_le_left _ _)).le
  have hys : dist y x < ε / (C + 1) := lt_of_lt_of_le hy (min_le_right _ _)
  calc
    dist (iteratedFDeriv ℝ m (f j) (x : EuclideanSpace ℝ (Fin d)))
        (iteratedFDeriv ℝ m (f j) (y : EuclideanSpace ℝ (Fin d)))
        ≤ C * dist y x := by simpa only [dist_eq_norm, Subtype.dist_eq, norm_sub_rev] using hLip j y hyr
    _ ≤ (C + 1) * dist y x := mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
    _ < ε := by simpa only [mul_comm] using (lt_div_iff₀ (by linarith : 0 < C + 1)).mp hys

private theorem exists_locallyUniform_jet_limits
    [FiniteDimensional ℝ E]
    {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : IsOpen Ω) (f : ℕ → EuclideanSpace ℝ (Fin d) → E)
    (hf : ∀ j, ContDiffOn ℝ ∞ (f j) Ω)
    (hbound : LocallyEventuallyBoundedDerivatives Ω f) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ g : (m : ℕ) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) [×m]→L[ℝ] E,
        ∀ m, TendstoLocallyUniformlyOn
          (fun j => iteratedFDeriv ℝ m (f (σ j))) (g m) atTop Ω := by
  classical
  let X := EuclideanSpace ℝ (Fin d)
  let J := fun m : ℕ => X [×m]→L[ℝ] E
  let : LocallyCompactSpace Ω := hΩ.locallyCompactSpace
  have : ∀ m, FiniteDimensional ℝ (J m) := by
    intro m
    induction m with
    | zero => exact (continuousMultilinearCurryFin0 ℝ X E).symm.toLinearEquiv.finiteDimensional
    | succ m ih => exact (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (m + 1) => X) E).symm.toLinearEquiv.finiteDimensional
  let u : ∀ m, ℕ → C(Ω, J m) := fun m j =>
    ⟨fun x => iteratedFDeriv ℝ m (f j) x,
      (equicontinuous_iteratedFDeriv hΩ f hf hbound m).continuous j⟩
  have hc (m : ℕ) : IsCompact (closure (range (u m))) := by
    apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (F := fun v : C(Ω, J m) => (v : Ω → J m))
      (𝔖 := {K | IsCompact K}) (fun _ h => h)
      (show Topology.IsClosedEmbedding (ContinuousMap.toUniformOnFunIsCompact :
        C(Ω, J m) → UniformOnFun Ω (J m) {K | IsCompact K}) from
        ⟨ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isEmbedding, by
          rw [ContinuousMap.range_toUniformOnFunIsCompact]
          exact UniformOnFun.isClosed_setOfPred_continuous CompactlyCoherentSpace.isCoherentWith⟩)
    · intro K hK
      have heq : Equicontinuous (fun v : range (u m) => (v.val : Ω → J m)) := by
        intro x V hV
        filter_upwards [equicontinuous_iteratedFDeriv hΩ f hf hbound m x V hV] with y hy v
        obtain ⟨j, hj⟩ := v.property
        simpa only [← hj, u, ContinuousMap.coe_mk] using hy j
      exact heq.equicontinuousOn K
    · intro K hK x hx
      obtain ⟨B, hB, hboundB⟩ := norm_iteratedFDeriv_le_on_compact hΩ f hf hbound
        (isCompact_singleton (x := (x : X))) (singleton_subset_iff.mpr x.property) m
      refine ⟨closedBall (0 : J m) B, isCompact_closedBall _ _, ?_⟩
      rintro v ⟨j, rfl⟩
      simpa only [mem_closedBall, dist_zero_right, u, ContinuousMap.coe_mk] using
        hboundB j x (mem_singleton _)
  have : SigmaCompactSpace Ω := inferInstance
  have : ∀ m, FirstCountableTopology C(Ω, J m) := fun m => by
    have : Filter.IsCountablyGenerated (uniformity C(Ω, J m)) := inferInstance
    exact UniformSpace.firstCountableTopology C(Ω, J m)
  obtain ⟨a, ha, σ, hσ, hlim⟩ :=
    Poincare.exists_strictMono_tendsto_of_eventually_mem_isCompact u
      (fun m => closure (range (u m))) hc
      (fun m => Eventually.of_forall fun j => subset_closure (mem_range_self j))
  let g : ∀ m, X → J m := fun m x => if hx : x ∈ Ω then a m ⟨x, hx⟩ else 0
  refine ⟨σ, hσ, g, fun m => ?_⟩
  rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
  have hg : g m ∘ Subtype.val = (a m : Ω → J m) := by
    funext x
    simp only [g, Function.comp_apply, dif_pos x.property]
  rw [hg]
  simpa only [u, Function.comp_apply, ContinuousMap.coe_mk] using
    (ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp (hlim m))

private theorem exists_smooth_of_locallyUniform_jet_limits
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {Ω : Set X} (hΩ : IsOpen Ω) (f : ℕ → X → Y)
    (hf : ∀ j, ContDiffOn ℝ ∞ (f j) Ω)
    (g : (m : ℕ) → X → X [×m]→L[ℝ] Y)
    (hg : ∀ m, TendstoLocallyUniformlyOn
      (fun j ↦ iteratedFDeriv ℝ m (f j)) (g m) atTop Ω) :
    ∃ F : X → Y, ContDiffOn ℝ ∞ F Ω ∧
      ∀ m, EqOn (iteratedFDeriv ℝ m F) (g m) Ω := by
  have hderiv (m : ℕ) (x : X) (hx : x ∈ Ω) :
      HasFDerivAt (g m)
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) ↦ X) Y
          (g (m + 1) x)) x := by
    apply limit_hasFDerivAt_of_tendstoLocallyUniformlyOn
      (f := fun j ↦ iteratedFDeriv ℝ m (f j))
      (g := g m) (g' := fun y ↦ continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (m + 1) ↦ X) Y (g (m + 1) y)) hΩ
      ((continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (m + 1) ↦ X) Y).isometry.uniformContinuous.comp_tendstoLocallyUniformlyOn
          (hg (m + 1)))
    · intro j y hy
      have hd := ((hf j y hy).contDiffAt (hΩ.mem_nhds hy)).differentiableAt_iteratedFDeriv
        (ENat.natCast_lt_of_coe_top_le_withTop (N := (∞ : ℕ∞ω)) le_rfl m)
      simpa only [fderiv_iteratedFDeriv, Function.comp_apply] using hd.hasFDerivAt
    · exact fun y hy ↦ (hg m).tendsto_at hy
    · exact hx
  let F : X → Y := fun x ↦ continuousMultilinearCurryFin0 ℝ X Y (g 0 x)
  have heq (m : ℕ) : EqOn (iteratedFDeriv ℝ m F) (g m) Ω := by
    induction m with
    | zero =>
      intro x hx
      simp [iteratedFDeriv_zero_eq_comp, F]
    | succ m ih =>
      intro x hx
      have hlocal : iteratedFDeriv ℝ m F =ᶠ[𝓝 x] g m :=
        Filter.eventuallyEq_of_mem (hΩ.mem_nhds hx) ih
      simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
      rw [hlocal.fderiv_eq, (hderiv m x hx).fderiv]
      exact LinearIsometryEquiv.symm_apply_apply _ _
  have hdiff (m : ℕ) : DifferentiableOn ℝ (iteratedFDerivWithin ℝ m F Ω) Ω := by
    apply (show DifferentiableOn ℝ (g m) Ω from
      fun x hx ↦ (hderiv m x hx).differentiableAt.differentiableWithinAt).congr
    intro x hx
    exact (iteratedFDerivWithin_of_isOpen m hΩ hx).trans (heq m hx)
  refine ⟨F, ?_, heq⟩
  exact contDiffOn_of_continuousOn_differentiableOn
    (fun m _ ↦ (hdiff m).continuousOn) (fun m _ ↦ hdiff m)

theorem eventually_norm_iteratedFDeriv_sub_le_of_closedBall
    {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : IsOpen Ω) (f : ℕ → EuclideanSpace ℝ (Fin d) → E)
    (hf : ∀ j, ContDiffOn ℝ ∞ (f j) Ω)
    (hbound : LocallyEventuallyBoundedDerivatives Ω f)
    {x : EuclideanSpace ℝ (Fin d)} {r : ℝ} (_hr : 0 < r)
    (hball : closedBall x r ⊆ Ω) (m : ℕ) :
    ∃ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ j ≥ N, ∀ y ∈ closedBall x r, ∀ z ∈ closedBall x r,
        ‖iteratedFDeriv ℝ m (f j) y - iteratedFDeriv ℝ m (f j) z‖ ≤
          C * ‖y - z‖ := by
  obtain ⟨B, hB⟩ := hbound (closedBall x r) (isCompact_closedBall x r) hball (m + 1)
  rcases eventually_atTop.1 hB with ⟨N, hN⟩
  refine ⟨N, max B 0, le_max_right _ _, ?_⟩
  intro j hj y hy z hz
  have hfj : ContDiffOn ℝ ∞ (f j) Ω := hf j
  have hderiv : ∀ w ∈ closedBall x r,
      DifferentiableAt ℝ (iteratedFDeriv ℝ m (f j)) w := by
    intro w hw
    exact (hfj w (hball hw)).contDiffAt (hΩ.mem_nhds (hball hw)) |>.differentiableAt_iteratedFDeriv
      (ENat.natCast_lt_of_coe_top_le_withTop (N := (∞ : ℕ∞ω)) le_rfl m)
  have hdiff : ∀ w ∈ closedBall x r,
      ‖fderiv ℝ (iteratedFDeriv ℝ m (f j)) w‖ ≤ max B 0 := by
    intro w hw
    rw [norm_fderiv_iteratedFDeriv]
    exact (hN j hj w hw).trans (le_max_left _ _)
  exact (convex_closedBall x r).norm_image_sub_le_of_norm_fderiv_le hderiv hdiff hz hy

structure SmoothSubsequenceExtraction
    (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (f : ℕ → EuclideanSpace ℝ (Fin d) → E) where

  subsequence : ℕ → ℕ

  subsequence_strictMono : StrictMono subsequence

  limit : EuclideanSpace ℝ (Fin d) → E

  limit_contDiffOn : ContDiffOn ℝ ∞ limit Ω

  iteratedFDeriv_tendsto_uniformlyOn :
    ∀ (m : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))), IsCompact K → K ⊆ Ω →
      TendstoUniformlyOn
        (fun j x ↦ iteratedFDeriv ℝ m (f (subsequence j)) x)
        (iteratedFDeriv ℝ m limit) atTop K

theorem SmoothSubsequenceExtraction.tendsto_iteratedFDeriv
    {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {f : ℕ → EuclideanSpace ℝ (Fin d) → E}
    (H : SmoothSubsequenceExtraction Ω f)
    (m : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) :
    TendstoUniformlyOn
      (fun j x ↦ iteratedFDeriv ℝ m (f (H.subsequence j)) x)
      (iteratedFDeriv ℝ m H.limit) atTop K :=
  H.iteratedFDeriv_tendsto_uniformlyOn m K hK hKΩ

theorem exists_smoothSubsequenceExtraction
    [FiniteDimensional ℝ E]
    {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : IsOpen Ω)
    (f : ℕ → EuclideanSpace ℝ (Fin d) → E)
    (hf : ∀ j, ContDiffOn ℝ ∞ (f j) Ω)
    (hbound : LocallyEventuallyBoundedDerivatives Ω f) :
    Nonempty (SmoothSubsequenceExtraction Ω f) := by
  obtain ⟨σ, hσ, g, hg⟩ := exists_locallyUniform_jet_limits hΩ f hf hbound
  obtain ⟨F, hF, heq⟩ := exists_smooth_of_locallyUniform_jet_limits hΩ
    (fun j => f (σ j)) (fun j => hf (σ j)) g hg
  refine ⟨⟨σ, hσ, F, hF, fun m K hK hKΩ => ?_⟩⟩
  have hconv := (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ).mp (hg m) K hKΩ hK
  exact hconv.congr_right (fun x hx => (heq m (hKΩ hx)).symm)

end Poincare.Analysis.Calculus
