import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Convex.Topology

set_option autoImplicit false

open Set Filter Metric
open scoped Topology ContDiff

namespace Poincare.AncientVolume

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [FiniteDimensional ℝ Y]

omit [FiniteDimensional ℝ Y] in
private theorem equicontinuous_within_jets
    {Ω : Set X} (hclosed : IsClosed Ω) (hconvex : Convex ℝ Ω)
    (hunique : UniqueDiffOn ℝ Ω) (f : ℕ → X → Y)
    (hf : ∀ j, ContDiffOn ℝ ∞ (f j) Ω)
    (hbound : ∀ K : Set X, IsCompact K → K ⊆ Ω → ∀ m : ℕ,
      ∃ B : ℝ, 0 ≤ B ∧ ∀ j x, x ∈ K → ‖iteratedFDerivWithin ℝ m (f j) Ω x‖ ≤ B)
    (m : ℕ) :
    Equicontinuous (fun j (x : Ω) => iteratedFDerivWithin ℝ m (f j) Ω x) := by
  intro x
  let K := Ω ∩ closedBall (x : X) 1
  obtain ⟨B, hB, hBbound⟩ := hbound K
    ((isCompact_closedBall (x : X) 1).inter_left hclosed) inter_subset_left (m + 1)
  have hLip (j : ℕ) (y : Ω) (hy : dist y x < 1) :
      ‖iteratedFDerivWithin ℝ m (f j) Ω (x : X) -
        iteratedFDerivWithin ℝ m (f j) Ω (y : X)‖ ≤ B * ‖(x : X) - y‖ := by
    apply (hconvex.inter (convex_closedBall (x : X) 1)).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z hz => ((hf j).differentiableOn_iteratedFDerivWithin
        (ENat.natCast_lt_of_coe_top_le_withTop (N := (∞ : ℕ∞ω)) le_rfl m)
        hunique z hz.1).hasFDerivWithinAt.mono inter_subset_left)
      (fun z hz => ?_) ⟨y.property, hy.le⟩ ⟨x.property, mem_closedBall_self zero_le_one⟩
    rw [norm_fderivWithin_iteratedFDerivWithin]
    exact hBbound j z hz
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  refine ⟨min 1 (ε / (B + 1)), lt_min zero_lt_one (div_pos hε (by linarith)), ?_⟩
  intro y hy j
  have hy1 : dist y x < 1 := lt_of_lt_of_le hy (min_le_left _ _)
  have hyε : dist y x < ε / (B + 1) := lt_of_lt_of_le hy (min_le_right _ _)
  calc
    dist (iteratedFDerivWithin ℝ m (f j) Ω (x : X))
        (iteratedFDerivWithin ℝ m (f j) Ω (y : X)) ≤ B * dist y x := by
      simpa only [dist_eq_norm, Subtype.dist_eq, norm_sub_rev] using hLip j y hy1
    _ ≤ (B + 1) * dist y x := mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
    _ < ε := by simpa only [mul_comm] using (lt_div_iff₀ (by linarith : 0 < B + 1)).mp hyε

private theorem exists_closed_jet_limits
    {Ω : Set X} (hclosed : IsClosed Ω) (hconvex : Convex ℝ Ω)
    (hunique : UniqueDiffOn ℝ Ω) (f : ℕ → X → Y)
    (hf : ∀ j, ContDiffOn ℝ ∞ (f j) Ω)
    (hbound : ∀ K : Set X, IsCompact K → K ⊆ Ω → ∀ m : ℕ,
      ∃ B : ℝ, 0 ≤ B ∧ ∀ j x, x ∈ K → ‖iteratedFDerivWithin ℝ m (f j) Ω x‖ ≤ B) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ g : (m : ℕ) → X → X [×m]→L[ℝ] Y,
        ∀ m, TendstoLocallyUniformlyOn
          (fun j => iteratedFDerivWithin ℝ m (f (σ j)) Ω) (g m) atTop Ω := by
  classical
  let J := fun m : ℕ => X [×m]→L[ℝ] Y
  let : LocallyCompactSpace Ω := hclosed.locallyCompactSpace
  let : SigmaCompactSpace Ω := hclosed.sigmaCompactSpace
  have : ∀ m, FiniteDimensional ℝ (J m) := by
    intro m
    induction m with
    | zero => exact (continuousMultilinearCurryFin0 ℝ X Y).symm.toLinearEquiv.finiteDimensional
    | succ m ih => exact (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (m + 1) => X) Y).symm.toLinearEquiv.finiteDimensional
  let u : ∀ m, ℕ → C(Ω, J m) := fun m j =>
    ⟨fun x => iteratedFDerivWithin ℝ m (f j) Ω x,
      (equicontinuous_within_jets hclosed hconvex hunique f hf hbound m).continuous j⟩
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
        filter_upwards [equicontinuous_within_jets hclosed hconvex hunique f hf hbound m x V hV]
          with y hy v
        obtain ⟨j, hj⟩ := v.property
        simpa only [← hj, u, ContinuousMap.coe_mk] using hy j
      exact heq.equicontinuousOn K
    · intro K hK x hx
      obtain ⟨B, hB, hboundB⟩ := hbound {x.val} isCompact_singleton
        (singleton_subset_iff.mpr x.property) m
      refine ⟨closedBall (0 : J m) B, isCompact_closedBall _ _, ?_⟩
      rintro v ⟨j, rfl⟩
      simpa only [mem_closedBall, dist_zero_right, u, ContinuousMap.coe_mk] using
        hboundB j x (mem_singleton _)
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

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] in
private theorem smooth_of_closed_jet_limits
    {Ω : Set X} (hclosed : IsClosed Ω) (hconvex : Convex ℝ Ω)
    (hne : (interior Ω).Nonempty) (f : ℕ → X → Y)
    (hf : ∀ j, ContDiffOn ℝ ∞ (f j) Ω)
    (g : (m : ℕ) → X → X [×m]→L[ℝ] Y)
    (hg : ∀ m, TendstoLocallyUniformlyOn
      (fun j => iteratedFDerivWithin ℝ m (f j) Ω) (g m) atTop Ω) :
    ∃ F : X → Y, ContDiffOn ℝ ∞ F Ω ∧
      ∀ m, EqOn (iteratedFDerivWithin ℝ m F Ω) (g m) Ω := by
  have hunique := uniqueDiffOn_convex hconvex hne
  have hm (m : ℕ) : (m : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr (le_top : (m : ℕ∞) ≤ ⊤)
  have hc (m : ℕ) : ContinuousOn (g m) Ω :=
    (hg m).continuousOn (Eventually.of_forall
      (fun j => (hf j).continuousOn_iteratedFDerivWithin (hm m) hunique)).frequently
  have hinterior (m : ℕ) (x : X) (hx : x ∈ interior Ω) :
      HasFDerivAt (g m)
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => X) Y
          (g (m + 1) x)) x := by
    apply Poincare.Analysis.Calculus.limit_hasFDerivAt_of_tendstoLocallyUniformlyOn
      (f := fun j => iteratedFDerivWithin ℝ m (f j) Ω)
      (g := g m) (g' := fun y => continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (m + 1) => X) Y (g (m + 1) y)) isOpen_interior
      ((continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (m + 1) => X) Y).isometry.uniformContinuous.comp_tendstoLocallyUniformlyOn
          ((hg (m + 1)).mono interior_subset))
    · intro j y hy
      have hd := ((hf j).differentiableOn_iteratedFDerivWithin
        (ENat.natCast_lt_of_coe_top_le_withTop (N := (∞ : ℕ∞ω)) le_rfl m)
        hunique y (interior_subset hy)).hasFDerivWithinAt.hasFDerivAt
          (mem_interior_iff_mem_nhds.mp hy)
      simpa only [fderivWithin_iteratedFDerivWithin, Function.comp_apply] using hd
    · exact fun y hy => (hg m).tendsto_at (interior_subset hy)
    · exact hx
  have hclosure : closure (interior Ω) = Ω :=
    (hconvex.closure_interior_eq_closure_of_nonempty_interior hne).trans hclosed.closure_eq
  have hderiv (m : ℕ) (x : X) (hx : x ∈ Ω) :
      HasFDerivWithinAt (g m)
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => X) Y
          (g (m + 1) x)) Ω x := by
    rw [← hclosure]
    apply hasFDerivWithinAt_closure_of_tendsto_fderiv
      (fun y hy => (hinterior m y hy).differentiableAt.differentiableWithinAt)
      hconvex.interior isOpen_interior
      (fun y hy => (hc m y (hclosure ▸ hy)).mono interior_subset)
    have hl := ((continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin (m + 1) => X) Y).continuous.continuousAt.comp_continuousWithinAt
        (hc (m + 1) x hx)).mono interior_subset
    exact hl.congr' (eventually_of_mem self_mem_nhdsWithin
      (fun y hy => (hinterior m y hy).fderiv.symm))
  let F : X → Y := fun x => continuousMultilinearCurryFin0 ℝ X Y (g 0 x)
  have heq (m : ℕ) : EqOn (iteratedFDerivWithin ℝ m F Ω) (g m) Ω := by
    induction m with
    | zero =>
      intro x hx
      simp [iteratedFDerivWithin_zero_eq_comp, F]
    | succ m ih =>
      intro x hx
      simp only [iteratedFDerivWithin_succ_eq_comp_left, Function.comp_apply]
      rw [((hderiv m x hx).congr ih (ih hx)).fderivWithin (hunique x hx)]
      exact LinearIsometryEquiv.symm_apply_apply _ _
  have hdiff (m : ℕ) : DifferentiableOn ℝ (iteratedFDerivWithin ℝ m F Ω) Ω := by
    intro x hx
    exact ((hderiv m x hx).congr (heq m) (heq m hx)).differentiableWithinAt
  exact ⟨F, contDiffOn_of_continuousOn_differentiableOn
    (fun m _ => (hdiff m).continuousOn) (fun m _ => hdiff m), heq⟩

theorem exists_smooth_subsequence_on_closed_convex
    {Ω : Set X} (hclosed : IsClosed Ω) (hconvex : Convex ℝ Ω)
    (hne : (interior Ω).Nonempty) (f : ℕ → X → Y)
    (hf : ∀ j, ContDiffOn ℝ ∞ (f j) Ω)
    (hbound : ∀ K : Set X, IsCompact K → K ⊆ Ω → ∀ m : ℕ,
      ∃ B : ℝ, 0 ≤ B ∧ ∀ j x, x ∈ K → ‖iteratedFDerivWithin ℝ m (f j) Ω x‖ ≤ B) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ F : X → Y, ContDiffOn ℝ ∞ F Ω ∧
      ∀ m K, IsCompact K → K ⊆ Ω → TendstoUniformlyOn
        (fun j => iteratedFDerivWithin ℝ m (f (σ j)) Ω)
        (iteratedFDerivWithin ℝ m F Ω) atTop K := by
  obtain ⟨σ, hσ, g, hg⟩ := exists_closed_jet_limits hclosed hconvex
    (uniqueDiffOn_convex hconvex hne) f hf hbound
  obtain ⟨F, hF, heq⟩ := smooth_of_closed_jet_limits hclosed hconvex hne
    (fun j => f (σ j)) (fun j => hf (σ j)) g hg
  refine ⟨σ, hσ, F, hF, fun m K hK hKΩ => ?_⟩
  have hconv := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    ((hg m).mono hKΩ)
  exact hconv.congr_right (fun x hx => (heq m (hKΩ hx)).symm)

end Poincare.AncientVolume
