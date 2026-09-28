import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Strips.Flattening
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.DisjointSupport








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SaddleLevel

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
local notation "IR2" => 𝓘(Real, Real × Real)




theorem exists_supported_ambient_strip_family_flattening
    {g : S2 → E3} (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    {v : E3} (hv : ‖v‖ = 1) (p : S2)
    (a b : Fin 2 → Real) (F : Fin 2 → OpenPartialHomeomorph (Real × Real) S2)
    {w c r R : Real} (hw : 0 < w) (hr : 0 < r) (hrw : r < w) (hrR : r < R)
    (hsource : ∀ i, (F i).source = Ioo (a i - w) (b i + w) ×ˢ Ioo (-w) w)
    (hF : ∀ i, ContMDiffOn IR2 (𝓡 2) ∞ (F i) (F i).source)
    (hFi : ∀ i, ContMDiffOn (𝓡 2) IR2 ∞ (F i).symm (F i).target)
    (hheight : ∀ i z, z ∈ (F i).source → inner Real v (g (F i z)) = c + z.2)
    (U : Fin 2 → Set (Real ∙ v)ᗮ) (hU : ∀ i, IsOpen (U i))
    (hUdisjoint : Pairwise (fun i j => Disjoint (U i) (U j)))
    (havoid : ∀ i, (Real ∙ v)ᗮ.orthogonalProjectionOnto (g p) ∉ U i)
    (hproject : ∀ i q, q ∈ (F i).target →
      (Real ∙ v)ᗮ.orthogonalProjectionOnto (g q) ∈ U i) :
    ∃ K : Set E3, IsCompact K ∧
      K ⊆ {x | |inner Real v x - c| ≤ R ∧
        (Real ∙ v)ᗮ.orthogonalProjectionOnto x ∈ U 0 ∪ U 1} ∧
      ∃ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ x, inner Real v (D x) = inner Real v x) ∧
        (∀ x, inner Real v x = c → D x = x) ∧
        (∀ x ∉ K, D x = x) ∧
        (∀ i t, t ∈ Icc (-r) r → ∀ s ∈ Icc (a i) (b i),
          D (g (F i (s, t))) = g (F i (s, 0)) + t • v) ∧
        ∃ V : Set E3, IsOpen V ∧ g p ∈ V ∧ EqOn D id V := by
  choose K hK hKU D hDh hDzero hDfix hDflat using fun i : Fin 2 =>
    exists_supported_ambient_strip_flattening hg hv (F i) hw hr hrw hrR
      (hsource i) (hF i) (hFi i) (hheight i) (hU i) (hproject i)
  let O : Fin 2 → Set E3 := fun i =>
    (fun x => (Real ∙ v)ᗮ.orthogonalProjectionOnto x) ⁻¹' U i
  have hKO (i : Fin 2) : K i ⊆ O i := fun x hx => (hKU i hx).2
  have hOdisjoint : Pairwise (fun i j => Disjoint (O i) (O j)) := by
    intro i j hij
    exact (hUdisjoint hij).preimage _
  obtain ⟨hcompact, _, hfix, hagree⟩ :=
    Diffeomorph.trans_compact_support_fin_two D K O hK hKO hOdisjoint hDfix
  let A := (D 0).trans (D 1)
  have hpnot : g p ∉ K 0 ∪ K 1 := by
    rintro (h0 | h1)
    · exact havoid 0 (hKO 0 h0)
    · exact havoid 1 (hKO 1 h1)
  refine ⟨K 0 ∪ K 1, hcompact, ?_, A, ?_, ?_, hfix, ?_,
    (K 0 ∪ K 1)ᶜ, hcompact.isClosed.isOpen_compl, hpnot,
    fun x hx => hfix x hx⟩
  · intro x hx
    rcases hx with h0 | h1
    · exact ⟨(hKU 0 h0).1, Or.inl (hKU 0 h0).2⟩
    · exact ⟨(hKU 1 h1).1, Or.inr (hKU 1 h1).2⟩
  · intro x
    exact (D 0).trans_preserves (D 1) (fun x => inner Real v x) (hDh 0) (hDh 1) x
  · intro x hx
    change D 1 (D 0 x) = x
    rw [hDzero 0 x hx, hDzero 1 x hx]
  · intro i t ht s hs
    have hst : (s, t) ∈ (F i).source := by
      rw [hsource i]
      exact ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩,
        ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
    have hmem : g (F i (s, t)) ∈ O i :=
      hproject i (F i (s, t)) ((F i).map_source hst)
    exact (hagree i hmem).trans (hDflat i t ht s hs)

end Poincare.Manifold.Schoenflies.SaddleLevel
