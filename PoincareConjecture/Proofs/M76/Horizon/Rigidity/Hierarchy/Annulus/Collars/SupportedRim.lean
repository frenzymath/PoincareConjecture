import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Collars.Mathlib.CompactBicollarRestriction
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Collars.RimRestriction










set_option autoImplicit false
open Set

namespace Poincare.Topology

theorem exists_phase_constant_bicollar_of_eq_off_compact
    {E X Y : Type*} [TopologicalSpace E] [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y]
    {K : Set E} (hK : IsCompact K) {r : ℝ} (hr : 0 < r)
    (c : E × ℝ → X)
    (hc : ContinuousOn c (K ×ˢ Icc (-r) r))
    (hi : Topology.IsEmbedding (fun z : (K ×ˢ Icc (-r) r : Set (E × ℝ)) => c z))
    (ho : IsOpen (c '' (K ×ˢ Ioo (-r) r)))
    {R : Set X} (hzero : c '' (K ×ˢ ({0} : Set ℝ)) = frontier R)
    (hside : ∀ z ∈ K ×ˢ Icc (-r) r, c z ∈ R ↔ 0 ≤ z.2)
    (q q' : C(X, Y))
    (hphase : ∀ z ∈ K ×ˢ Icc (-r) r, q (c z) = q (c (z.1, 0)))
    {A : Set X} (hA : IsCompact A) (hAR : A ⊆ interior R)
    (hfixed : ∀ x ∉ A, q' x = q x) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ r / 2 ∧
      ContinuousOn c (K ×ˢ Icc (-delta) delta) ∧
      Topology.IsEmbedding
        (fun z : (K ×ˢ Icc (-delta) delta : Set (E × ℝ)) => c z) ∧
      IsOpen (c '' (K ×ˢ Ioo (-delta) delta)) ∧
      (∀ z ∈ K ×ˢ Icc (-delta) delta, c z ∈ R ↔ 0 ≤ z.2) ∧
      (∀ z ∈ K ×ˢ Icc (-delta) delta, q' (c z) = q' (c (z.1, 0))) := by
  have hzavoid (x : E) (hx : x ∈ K) : c (x, 0) ∈ Aᶜ := by
    intro h
    have hz : c (x, 0) ∈ frontier R := hzero ▸ mem_image_of_mem c ⟨hx, rfl⟩
    exact disjoint_left.mp disjoint_interior_frontier (hAR h) hz
  obtain ⟨delta, hd, hdr, havoid, hopen⟩ :=
    exists_compact_bicollar_restriction hK c hr hc hi ho hA.isClosed.isOpen_compl hzavoid
  have hdle : delta ≤ r := by linarith
  have hsub : K ×ˢ Icc (-delta) delta ⊆ K ×ˢ Icc (-r) r := by
    intro z hz
    exact ⟨hz.1, by linarith [hz.2.1], le_trans hz.2.2 hdle⟩
  refine ⟨delta, hd, hdr, hc.mono hsub,
    hi.comp (Topology.IsEmbedding.inclusion hsub), hopen delta hd le_rfl,
    fun z hz => hside z (hsub hz), ?_⟩
  intro z hz
  rw [hfixed (c z) (havoid hz), hfixed (c (z.1, 0)) (hzavoid z.1 hz.1)]
  exact hphase z (hsub hz)

theorem fundamentalGroup_supported_phase_rim_complement_surjective
    {E X Y : Type*} [TopologicalSpace E] [Zero E]
    [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]
    {K : Set E} (hK : IsCompact K) {r : ℝ} (hr : 0 < r)
    (c : E × ℝ → X)
    (hc : ContinuousOn c (K ×ˢ Icc (-r) r))
    (hi : Topology.IsEmbedding (fun z : (K ×ˢ Icc (-r) r : Set (E × ℝ)) => c z))
    (ho : IsOpen (c '' (K ×ˢ Ioo (-r) r)))
    {R : Set X} (hzero : c '' (K ×ˢ ({0} : Set ℝ)) = frontier R)
    (hside : ∀ z ∈ K ×ˢ Icc (-r) r, c z ∈ R ↔ 0 ≤ z.2)
    (q q' : C(X, Y))
    (hphase : ∀ z ∈ K ×ˢ Icc (-r) r, q (c z) = q (c (z.1, 0)))
    {A : Set X} (hA : IsCompact A) (hAR : A ⊆ interior R)
    (hfixed : ∀ x ∉ A, q' x = q x) (theta : Y) :
    let S := R ∩ q' ⁻¹' {theta}
    let B := (Subtype.val : S → X) ⁻¹' frontier R
    ∀ x : ↥Bᶜ, Function.Surjective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥Bᶜ, S)) x) := by
  obtain ⟨delta, hd, _, hc', hi', ho', hs', hp'⟩ :=
    exists_phase_constant_bicollar_of_eq_off_compact hK hr c hc hi ho hzero hside
      q q' hphase hA hAR hfixed
  exact fundamentalGroup_phase_rim_complement_surjective hK hd c hc' hi' ho'
    hzero hs' q' hp' theta

end Poincare.Topology
