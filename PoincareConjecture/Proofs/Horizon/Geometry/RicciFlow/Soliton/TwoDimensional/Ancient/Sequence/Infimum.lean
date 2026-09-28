import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Sequence.DiagonalBound
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Sequence.Coercivity
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Sequences










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.AncientKappaSolution

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]


noncomputable def spatialReducedLengthInfimum (K : AncientKappaSolution 2 M)
    (p : M) (τ : ℝ) : ℝ :=
  sInf (range (fun q => reducedLength K.flow 0 p q τ))

theorem bddBelow_range_reducedLength (K : AncientKappaSolution 2 M)
    (p : M) (τ : ℝ) : BddBelow (range (fun q => reducedLength K.flow 0 p q τ)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨q, rfl⟩
  exact K.reducedLength_nonneg p q τ

theorem spatialReducedLengthInfimum_nonneg (K : AncientKappaSolution 2 M)
    (p : M) (τ : ℝ) : 0 ≤ K.spatialReducedLengthInfimum p τ := by
  apply Real.sInf_nonneg
  rintro _ ⟨q, rfl⟩
  exact K.reducedLength_nonneg p q τ

theorem spatialReducedLengthInfimum_le (K : AncientKappaSolution 2 M)
    (p q : M) (τ : ℝ) :
    K.spatialReducedLengthInfimum p τ ≤ reducedLength K.flow 0 p q τ :=
  csInf_le (K.bddBelow_range_reducedLength p τ) (mem_range_self q)

theorem tendsto_spatialReducedLengthInfimum_zero (K : AncientKappaSolution 2 M)
    (p : M) : Tendsto (K.spatialReducedLengthInfimum p) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (K.tendsto_reducedLength_self_zero p)
  · exact fun τ => K.spatialReducedLengthInfimum_nonneg p τ
  · exact fun τ => K.spatialReducedLengthInfimum_le p p τ


theorem exists_convergent_reducedLength_minimizing_sequence (K : AncientKappaSolution 2 M)
    (p : M) {τ : ℝ} (hτ : 0 < τ) :
    ∃ q : ℕ → M, ∃ qLimit : M,
      Tendsto q atTop (𝓝 qLimit) ∧
      Antitone (fun k => reducedLength K.flow 0 p (q k) τ) ∧
      Tendsto (fun k => reducedLength K.flow 0 p (q k) τ) atTop
        (𝓝 (K.spatialReducedLengthInfimum p τ)) := by
  classical
  obtain ⟨u, huanti, hulim, humem⟩ := exists_seq_tendsto_sInf
    (range_nonempty (f := fun q => reducedLength K.flow 0 p q τ))
    (K.bddBelow_range_reducedLength p τ)
  choose q hq using humem
  dsimp only at hq
  have hcompact := K.isCompact_closure_reducedLength_sublevel p hτ (u 0)
  have hmem (k : ℕ) : q k ∈ closure {x | reducedLength K.flow 0 p x τ ≤ u 0} := by
    apply subset_closure
    change reducedLength K.flow 0 p (q k) τ ≤ u 0
    rw [hq k]
    exact huanti (Nat.zero_le k)
  obtain ⟨qLimit, _, σ, hσ, hlim⟩ := hcompact.tendsto_subseq hmem
  refine ⟨q ∘ σ, qLimit, hlim, ?_, ?_⟩
  · intro i j hij
    simpa only [Function.comp_apply, hq] using huanti (hσ.monotone hij)
  · simpa only [Function.comp_def, hq, spatialReducedLengthInfimum] using
      hulim.comp hσ.tendsto_atTop

end PoincareConjecture.AncientKappaSolution
