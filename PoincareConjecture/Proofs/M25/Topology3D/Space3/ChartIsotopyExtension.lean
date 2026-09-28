import PoincareConjecture.Proofs.M25.Topology3D.Space3.ChartTimeField
import PoincareConjecture.Proofs.M25.Topology3D.Space3.LocalFieldIsotopy












set_option autoImplicit false

open Set
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]



theorem exists_ambient_isotopy_of_chart
    (e : OpenPartialHomeomorph (ℝ × E) (ℝ × E))
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (htime : ∀ p ∈ e.source, (e p).1 = p.1)
    (A : E →L[ℝ] F) (hA : ∀ p ∈ e.source, A (e p).2 = A p.2)
    {S : Set E} (hS : IsCompact S) {a b s : ℝ} (hs : s ∈ Ioo a b)
    (hsource : Icc a b ×ˢ S ⊆ e.source) :
    ∃ Φ : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      ContDiff ℝ ∞ (fun p : ℝ × E => Φ p.1 p.2) ∧
      (∀ x, Φ s x = x) ∧
      (∀ x ∈ S, ∀ t ∈ Ioo a b, Φ t (e (s, x)).2 = (e (t, x)).2) ∧
      (∃ C : Set E, IsCompact C ∧ C ⊆ Prod.snd '' e.target ∧
        ∀ t x, x ∉ C → Φ t x = x) ∧
      ∀ t x, A (Φ t x) = A x := by
  have hK : IsCompact (e '' (Icc a b ×ˢ S)) :=
    (isCompact_Icc.prod hS).image_of_continuousOn (e.continuousOn.mono hsource)
  have hKU : e '' (Icc a b ×ˢ S) ⊆ e.target := by
    rintro p ⟨q, hq, rfl⟩
    exact e.map_source (hsource hq)
  let c := fun t (x : S) => (e (t, (x : E))).2
  have htracks (x : S) (t : ℝ) (ht : t ∈ Ioo a b) :
      (t, c t x) ∈ e '' (Icc a b ×ˢ S) := by
    refine ⟨(t, (x : E)), ⟨Ioo_subset_Icc_self ht, x.2⟩, ?_⟩
    exact Prod.ext (htime _ (hsource ⟨Ioo_subset_Icc_self ht, x.2⟩)) rfl
  have hc (x : S) (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt (fun z => c z x) (chartTimeField e (t, c t x)) t :=
    chartTimeField_track e he htime t x (hsource ⟨Ioo_subset_Icc_self ht, x.2⟩)
  obtain ⟨Φ, hΦ, hzero, htrack, hsupp, hlinear⟩ :=
    exists_ambient_isotopy_of_localField hK e.open_target hKU (chartTimeField e)
      (chartTimeField_contDiffOn e he hi) A (chartTimeField_preserves_linear e he A hA)
      c hs htracks hc
  exact ⟨Φ, hΦ, hzero, fun x hx t ht => htrack ⟨x, hx⟩ t ht, hsupp, hlinear⟩

end PoincareConjecture.M25.Topology3D
