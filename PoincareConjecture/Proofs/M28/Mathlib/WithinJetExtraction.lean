import PoincareConjecture.Proofs.M28.Mathlib.WithinJetBounds
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.Sequences

set_option autoImplicit false

open Set Filter Metric
open scoped ContDiff Topology

theorem exists_common_locallyUniform_withinJet_limits
    {E F : ℕ → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    [∀ i, FiniteDimensional ℝ (F i)]
    (S : ∀ i, Set (E i)) [∀ i, LocallyCompactSpace (S i)]
    (hconv : ∀ i, Convex ℝ (S i)) (hS : ∀ i, UniqueDiffOn ℝ (S i))
    (f : ∀ i, ℕ → E i → F i) (hf : ∀ i j, ContDiffOn ℝ ∞ (f i j) (S i))
    (hbound : ∀ i K, IsCompact K → K ⊆ S i → ∀ m : ℕ,
      ∃ B : ℝ, ∀ᶠ j in atTop, ∀ x ∈ K,
        ‖iteratedFDerivWithin ℝ m (f i j) (S i) x‖ ≤ B) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ g : ∀ i m, E i → E i [×m]→L[ℝ] F i,
        ∀ i m, TendstoLocallyUniformlyOn
          (fun j => iteratedFDerivWithin ℝ m (f i (σ j)) (S i)) (g i m) atTop (S i) := by
  classical
  let Jet := fun p : ℕ × ℕ => E p.1 [×p.2]→L[ℝ] F p.1
  have hfinite : ∀ p, FiniteDimensional ℝ (Jet p) := by
    rintro ⟨i, m⟩
    dsimp only [Jet]
    induction m with
    | zero =>
      exact (continuousMultilinearCurryFin0 ℝ (E i) (F i)).symm.toLinearEquiv.finiteDimensional
    | succ m ih => exact (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (m + 1) => E i) (F i)).symm.toLinearEquiv.finiteDimensional
  let := hfinite
  have hequi (i m : ℕ) := equicontinuous_iteratedFDerivWithin
    (hconv i) (hS i) (f i) (hf i) (hbound i) m
  let u : ∀ p : ℕ × ℕ, ℕ → C(S p.1, Jet p) := fun p j =>
    ⟨fun x => iteratedFDerivWithin ℝ p.2 (f p.1 j) (S p.1) x,
      (hequi p.1 p.2).continuous j⟩
  have hc (p : ℕ × ℕ) : IsCompact (closure (range (u p))) := by
    apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (F := fun v : C(S p.1, Jet p) => (v : S p.1 → Jet p))
      (𝔖 := {K | IsCompact K}) (fun _ h => h)
      (show Topology.IsClosedEmbedding (ContinuousMap.toUniformOnFunIsCompact :
        C(S p.1, Jet p) → UniformOnFun (S p.1) (Jet p) {K | IsCompact K}) from
        ⟨ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isEmbedding, by
          rw [ContinuousMap.range_toUniformOnFunIsCompact]
          exact UniformOnFun.isClosed_setOfPred_continuous CompactlyCoherentSpace.isCoherentWith⟩)
    · intro K _
      have heq : Equicontinuous (fun v : range (u p) => (v.val : S p.1 → Jet p)) := by
        intro x V hV
        filter_upwards [hequi p.1 p.2 x V hV] with y hy v
        obtain ⟨j, hj⟩ := v.property
        simpa only [← hj, u, ContinuousMap.coe_mk] using hy j
      exact heq.equicontinuousOn K
    · intro K _ x _
      obtain ⟨B, _, hB⟩ := norm_iteratedFDerivWithin_le_on_compact
        (hS p.1) (f p.1) (hf p.1) (isCompact_singleton (x := (x : E p.1)))
        (singleton_subset_iff.mpr x.property) p.2
        (hbound p.1 _ isCompact_singleton (singleton_subset_iff.mpr x.property) p.2)
      refine ⟨closedBall (0 : Jet p) B, isCompact_closedBall _ _, ?_⟩
      rintro v ⟨j, rfl⟩
      simpa only [mem_closedBall, dist_zero_right, u, ContinuousMap.coe_mk] using
        hB j x (mem_singleton _)
  have : ∀ p : ℕ × ℕ, FirstCountableTopology C(S p.1, Jet p) := fun p => by
    have : SigmaCompactSpace (S p.1) := inferInstance
    have : Filter.IsCountablyGenerated (uniformity C(S p.1, Jet p)) := inferInstance
    exact UniformSpace.firstCountableTopology C(S p.1, Jet p)
  obtain ⟨a, _, σ, hσ, hlim⟩ := (isCompact_pi_infinite hc).tendsto_subseq
    (fun j p => subset_closure (mem_range_self (f := u p) j))
  let g : ∀ i m, E i → E i [×m]→L[ℝ] F i :=
    fun i m x => if hx : x ∈ S i then a (i, m) ⟨x, hx⟩ else 0
  refine ⟨σ, hσ, g, fun i m => ?_⟩
  rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
  have hg : g i m ∘ Subtype.val = (a (i, m) : S i → Jet (i, m)) := by
    funext x
    simp only [g, Function.comp_apply, dif_pos x.property]
  rw [hg]
  simpa only [u, Function.comp_apply, ContinuousMap.coe_mk] using
    (ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp ((tendsto_pi_nhds.mp hlim) (i, m)))
