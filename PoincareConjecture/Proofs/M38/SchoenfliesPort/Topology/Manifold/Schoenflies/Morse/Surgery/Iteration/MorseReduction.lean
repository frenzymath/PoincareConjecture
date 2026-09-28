import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Construction
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.LeafBands
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.ProtectedGerms
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Perturbation.DistinctValues
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.RegularLevel.Cuts







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies



noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1




structure SphereMorseReduction (f : S2 -> E3) where
  v : S2
  D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞
  compact_support : ∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, D y = y
  embedding : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (fun p => D (f p))
  finite_critical : {p : S2 | mfderiv (𝓡 2) 𝓘(Real, Real)
    (fun q => inner Real (v : E3) (D (f q))) p = 0}.Finite
  distinct_values : InjOn (fun p => inner Real (v : E3) (D (f p)))
    {p : S2 | mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (v : E3) (D (f q))) p = 0}
  coordinates : ∀ p : S2, mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (v : E3) (D (f q))) p = 0 ->
    ∃ (e : OpenPartialHomeomorph E2 S2) (σ : Fin 2 -> Real),
      (∀ i, σ i = -1 ∨ σ i = 1) ∧ 0 ∈ e.source ∧ e 0 = p ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
      ∀ x ∈ e.source, inner Real (v : E3) (D (f (e x))) =
        inner Real (v : E3) (D (f p)) + ∑ i : Fin 2, σ i * x i ^ 2
  cuts : Finset Real
  regular : ∀ c ∈ cuts, ∀ p, inner Real (v : E3) (D (f p)) = c ->
    mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real (v : E3) (D (f q))) p ≠ 0
  separates_critical : ∀ p q : S2,
    mfderiv (𝓡 2) 𝓘(Real, Real) (fun r => inner Real (v : E3) (D (f r))) p = 0 ->
    mfderiv (𝓡 2) 𝓘(Real, Real) (fun r => inner Real (v : E3) (D (f r))) q = 0 ->
    inner Real (v : E3) (D (f q)) ∈ connectedComponentIn (cuts : Set Real)ᶜ
      (inner Real (v : E3) (D (f p))) -> p = q
  tree : SphereSurgeryTree v cuts (fun p => D (f p))
  protects_critical_values : tree.Protects
    ((fun p => inner Real (v : E3) (D (f p))) ''
      {p : S2 | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun q => inner Real (v : E3) (D (f q))) p = 0})
  preserves_caps : tree.PreservesCaps




theorem nonempty_sphereMorseReduction
    (f : S2 -> E3) (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f) :
    Nonempty (SphereMorseReduction f) := by
  classical
  obtain ⟨v, D, hDc, hDf, hfinite, hcritical, hinj, _, hcoordinates⟩ :=
    exists_morse_height_with_distinct_critical_values f hf (ε := 1) (by norm_num)
  let h : S2 -> Real := fun p => inner Real (v : E3) (D (f p))
  have hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h :=
    (innerSL Real (v : E3)).contMDiff.comp hDf.contMDiff
  have hC : {p | mfderiv (𝓡 2) 𝓘(Real, Real) h p = 0}.Finite :=
    hfinite.subset (fun p hp => (hcritical p).mp hp)
  have hdistinct : InjOn h {p | mfderiv (𝓡 2) 𝓘(Real, Real) h p = 0} := by
    intro p hp q hq heq
    exact hinj ((hcritical p).mp hp) ((hcritical q).mp hq) heq
  obtain ⟨A, hA, hregular, _, hseparates⟩ :=
    exists_finite_regular_cuts_of_distinct_critical_values hh hC hdistinct
  have hreg : ∀ c ∈ hA.toFinset, ∀ p, h p = c ->
      mfderiv (𝓡 2) 𝓘(Real, Real) h p ≠ 0 := by
    simpa only [hA.mem_toFinset] using hregular
  have hdisj : Disjoint (hA.toFinset : Set Real)
      (h '' {p | mfderiv (𝓡 2) 𝓘(Real, Real) h p = 0}) := by
    apply Set.disjoint_left.mpr
    rintro k hk ⟨p, hp, hpk⟩
    exact hreg k hk p hpk hp
  obtain ⟨tree, hprotects, hcaps⟩ := exists_sphereSurgeryTree_preserving_caps hDf
    (mem_sphere_zero_iff_norm.mp v.property) hA.toFinset hreg _
      (hC.image h).isCompact hdisj
  refine ⟨{
    v := v
    D := D
    compact_support := hDc
    embedding := hDf
    finite_critical := hC
    distinct_values := hdistinct
    coordinates := hcoordinates
    cuts := hA.toFinset
    regular := hreg
    separates_critical := ?_
    tree := tree
    protects_critical_values := hprotects
    preserves_caps := hcaps
  }⟩
  simpa only [hA.coe_toFinset] using hseparates

namespace SphereMorseReduction

variable {f : S2 -> E3} (M : SphereMorseReduction f)



theorem exists_leaf_at_critical_point {p : S2}
    (hp : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (M.v : E3) (M.D (f q))) p = 0) :
    ∃ g ∈ M.tree.leaves, g =ᶠ[𝓝 p] (fun q => M.D (f q)) := by
  exact M.tree.exists_protected_point_in_leaf M.protects_critical_values ⟨p, hp, rfl⟩



theorem leaf_height_band {g : S2 -> E3} (hg : g ∈ M.tree.leaves) :
    ∃ b ∈ (M.cuts : Set Real)ᶜ,
      range (fun q => inner Real (M.v : E3) (g q)) ⊆
        connectedComponentIn (M.cuts : Set Real)ᶜ b ∧
      IsConnected (connectedComponentIn (M.cuts : Set Real)ᶜ b) ∧
      {p : S2 | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun q => inner Real (M.v : E3) (M.D (f q))) p = 0 ∧
        inner Real (M.v : E3) (M.D (f p)) ∈
          connectedComponentIn (M.cuts : Set Real)ᶜ b}.Subsingleton := by
  exact M.tree.height_band_of_mem_leaves hg M.separates_critical

end SphereMorseReduction

end Poincare.Manifold.Schoenflies

end

end M38Schoenflies
