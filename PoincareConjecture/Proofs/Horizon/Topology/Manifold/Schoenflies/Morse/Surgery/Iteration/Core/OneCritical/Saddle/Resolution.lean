import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.Saddle.Flattening
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Resolution.Strips.Components
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.SaddleEnds.ResolutionCircles
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.SaddleEnds.EndCount








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SphereMorseReduction

open SaddleLevel SphereSurgeryCoreCap

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1




theorem exists_terminal_saddle_cut_resolution
    {f : S2 → E3} (M : SphereMorseReduction f)
    {g : S2 → E3} (hg : g ∈ M.tree.leaves)
    (P : SphereSurgeryPath (M.v : E3) (fun p => M.D (f p)) g)
    (hP : P.Protects ((fun p => inner Real (M.v : E3) (M.D (f p))) ''
      {p | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun q => inner Real (M.v : E3) (M.D (f q))) p = 0}))
    (hcaps : P.PreservesCaps) {p : S2} (hp : p ∈ P.core)
    (hc : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (M.v : E3) (g q)) p = 0)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2)
    {ε : Real} (hε : 0 < ε) :
    ∃ r δ : Real, 0 < r ∧ r < ε ∧ closedSquare r ⊆ e.source ∧
      0 < δ ∧ δ < ε ∧ δ < r ^ 2 ∧
      ∀ t : Real, 0 < t → t ≤ δ →
        ∃ A : AnnularEndFamily (M.v : E3) g
          ((fun q => inner Real (M.v : E3) (M.D (f q))) ''
            {q | mfderiv (𝓡 2) 𝓘(Real, Real)
              (fun y => inner Real (M.v : E3) (M.D (f y))) q = 0}) P.core,
          A.lowerCut = inner Real (M.v : E3) (g p) - t ∧
          A.upperCut = inner Real (M.v : E3) (g p) + t ∧
          A.caps.length = 3 ∧
          ((Nat.card A.LowerCutIndex = 1 ∧
            ∃ E : Fin 2 ≃ A.UpperCutIndex,
              ∀ i, positivePatchArc e r t i ⊆ range (A.upperCutCircle (E i))) ∨
           (Nat.card A.UpperCutIndex = 1 ∧
            ∃ E : Fin 2 ≃ A.LowerCutIndex,
              ∀ i, negativePatchArc e r t i ⊆ range (A.lowerCutCircle (E i)))) := by
  let h := fun q => inner Real (M.v : E3) (g q)
  obtain ⟨ε₀, hε₀, hfamilies⟩ :=
    M.exists_terminal_annular_end_family hg P hP hcaps hp hc
  obtain ⟨r, w, η, a, b, F, hr, hrε, hrs, hw, hη, hηw, hηε, _, hFs,
      _, _, hheight, hdisjoint, _, hband, ⟨a₀, b₀, hchain, hcentral, hends⟩,
      hpair, _⟩ := M.exists_terminal_saddle_band_flattening hg P hP hcaps hp hc
        e he0 hep he hei hform (lt_min hε hε₀)
  have hrect (i : Fin 2) :
      Icc (a i) (b i) ×ˢ Icc (-η) η ⊆ (F i).source := by
    rintro ⟨s, t⟩ ⟨hs, ht⟩
    rw [hFs i]
    exact ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩,
      ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
  obtain ⟨δ, hδ, hδη, hδr, hresolution⟩ :=
    exists_resolved_level_components e hr hrs hform F a b a₀ b₀ hη hchain
      hrect hheight hdisjoint hcentral hends hband hpair
  refine ⟨r, δ, hr, hrε.trans_le (min_le_left _ _), hrs, hδ,
    (hδη.trans hηε).trans_le (min_le_left _ _), hδr, ?_⟩
  intro t ht htδ
  have htr := htδ.trans_lt hδr
  have htε₀ : t ≤ ε₀ :=
    ((htδ.trans_lt hδη).trans hηε).le.trans (min_le_right _ _)
  obtain ⟨A, hlow, hupp⟩ := hfamilies t ht htε₀
  have hlevel (c : Real) : h ⁻¹' {c} = {q | inner Real (M.v : E3) (g q) = c} := by
    ext q
    simp [h]
  have hzero : 0 ∈ Icc (-hyperbolaRadius r t) (hyperbolaRadius r t) :=
    ⟨neg_nonpos.mpr (hyperbolaRadius_pos htr).le, (hyperbolaRadius_pos htr).le⟩
  rcases hresolution with hnegative | hpositive
  · obtain ⟨hconn, hcard, C, hdisj, harcs, hC⟩ := hnegative t ht htδ
    have hcardA : Nat.card
        (ConnectedComponents {q | inner Real (M.v : E3) (g q) = A.lowerCut}) = 2 := by
      rw [hlow, ← hlevel]
      exact hcard
    have hCA : ∀ i q, q ∈ C i → connectedComponentIn
        {q | inner Real (M.v : E3) (g q) = A.lowerCut} q = C i := by
      simpa only [hlow, preimage, mem_singleton_iff] using hC
    obtain ⟨E, hE⟩ := A.exists_lowerCutCircle_equiv_of_two_components hcardA C hCA
      hdisj (fun i => e (negativeLevelArc t i 0))
      (fun i => harcs i (mem_image_of_mem e (mem_image_of_mem _ hzero)))
    have hone : Nat.card A.UpperCutIndex = 1 :=
      A.card_upperCutIndex_eq_one_of_isConnected
        (by simpa only [hupp, preimage, mem_singleton_iff] using hconn)
    have htwo := A.card_lowerCutIndex_eq_two_of_card_connectedComponents hcardA
    exact ⟨A, hlow, hupp, A.caps_length_eq_three_of_cut_counts (Or.inr ⟨htwo, hone⟩),
      Or.inr ⟨hone, E, fun i => (harcs i).trans (hE i).superset⟩⟩
  · obtain ⟨hconn, hcard, C, hdisj, harcs, hC⟩ := hpositive t ht htδ
    have hcardA : Nat.card
        (ConnectedComponents {q | inner Real (M.v : E3) (g q) = A.upperCut}) = 2 := by
      rw [hupp, ← hlevel]
      exact hcard
    have hCA : ∀ i q, q ∈ C i → connectedComponentIn
        {q | inner Real (M.v : E3) (g q) = A.upperCut} q = C i := by
      simpa only [hupp, preimage, mem_singleton_iff] using hC
    obtain ⟨E, hE⟩ := A.exists_upperCutCircle_equiv_of_two_components hcardA C hCA
      hdisj (fun i => e (positiveLevelArc t i 0))
      (fun i => harcs i (mem_image_of_mem e (mem_image_of_mem _ hzero)))
    have hone : Nat.card A.LowerCutIndex = 1 :=
      A.card_lowerCutIndex_eq_one_of_isConnected
        (by simpa only [hlow, preimage, mem_singleton_iff] using hconn)
    have htwo := A.card_upperCutIndex_eq_two_of_card_connectedComponents hcardA
    exact ⟨A, hlow, hupp, A.caps_length_eq_three_of_cut_counts (Or.inl ⟨hone, htwo⟩),
      Or.inl ⟨hone, E, fun i => (harcs i).trans (hE i).superset⟩⟩

end Poincare.Manifold.Schoenflies.SphereMorseReduction
