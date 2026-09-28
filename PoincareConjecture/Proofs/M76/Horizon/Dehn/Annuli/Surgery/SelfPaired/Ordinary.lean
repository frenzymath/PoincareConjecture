import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.SelfPaired.ReflectionInsertion
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.ReflectionOpenSource
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.ReflectionDecrease
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.OrdinaryPreservation

set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_reflection_ordinary_map
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f : P2 → X} {R : Set X}
    (J : SimplicialComplex ℝ P2) (hJ : J.faces.Finite)
    (hf : PolyhedralPLInCharts e f J.space) (he : PLDomain e R)
    (hin : MapsTo f J.space R)
    (hfront : ∀ x ∈ J.space, f x ∈ frontier R ↔ x ∈ frontier J.space)
    (hcollision : Disjoint (doubleLocusOn f J.space) (frontier J.space))
    (hcross : ∀ x ∈ J.space, ∀ y ∈ J.space, x ≠ y → f x = f y →
      Nonempty (RawSourceCrossing e f J.space R x y))
    {L d b : ℝ} (hd : 0 < d) (hwidth : 4 * d < L) (hb : 0 < b) (hbd : b < d)
    (τ : (P2 × ℝ) → X) (hτ : PolyhedralPLInCharts e τ (singleReflectionTube L d))
    (hfib : ∀ z ∈ singleReflectionTube L d, ∀ w ∈ singleReflectionTube L d,
      τ z = τ w ↔ z = w ∨
        (z.1 = (w.1.1, -w.1.2) ∧
          ((z.2 = 0 ∧ w.2 = 2 * L) ∨ (z.2 = 2 * L ∧ w.2 = 0))))
    (hτR : τ '' singleReflectionTube L d ⊆ interior R)
    {T : Set P2} (hT : T ⊆ interior J.space)
    (c : squareAnnulus L d ≃ₜ T) (hc : c.IsFinitePL)
    (hsource : ∀ s ∈ Icc 0 (4 * L), ∀ u : Icc (-d) d,
      f (c ⟨annulusMap L (by linarith) ((s : AddCircle (4 * L)), u),
        annulus_period_point_mem hd hwidth _ u⟩) =
        if s ≤ 2 * L then τ ((u, u), s) else τ ((u, -u), s - 2 * L))
    (hpreimage : J.space ∩ f ⁻¹' (τ '' singleReflectionTube L d) = T)
    (M : SourceCircleDecomposition f J.space) (i : M.Index)
    (hmiddle : (fun p : squareAnnulus L d ↦ (c p : P2)) ''
      {p | depth L p = 0} = M.pieces i)
    (htrace : doubleLocusOn f J.space ∩ T = M.pieces i) :
    ∃ g : P2 → X, PolyhedralPLInCharts e g J.space ∧ MapsTo g J.space R ∧
      EqOn g f (frontier J.space) ∧
      (∀ x ∈ J.space, g x ∈ frontier R ↔ x ∈ frontier J.space) ∧
      Disjoint (doubleLocusOn g J.space) (frontier J.space) ∧
      IsCompact (doubleLocusOn g J.space) ∧
      (∀ x ∈ J.space, ∀ y ∈ J.space, x ≠ y → g x = g y →
        Nonempty (RawSourceCrossing e g J.space R x y)) ∧
      IsLocallyInjective (fun x : J.space ↦ g x) ∧
      Nonempty (SourceCircleDecomposition g J.space) ∧
      Nat.card (ConnectedComponents (doubleLocusOn g J.space)) <
        Nat.card (ConnectedComponents (doubleLocusOn f J.space)) := by
  obtain ⟨K, g, hK, hKs, hcover, _, hg, hkeep, hgin, hrim, hgfront,
    _, _, hrel, hnew, _⟩ :=
    exists_reflection_insertion J hJ hf he hin hfront hd hwidth hb hbd τ hτ hfib hτR
      hT c hc hsource hpreimage
  have hKS : K.space ⊆ J.space := fun x hx ↦ hcover.subset (Or.inl hx)
  have hTC : IsClosed T := hc.symm.choose_spec.1.isCompact.isClosed
  have hinside : M.pieces i ⊆ interior T := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := hmiddle.symm.subset hx
    by_contra hn
    have hfT : (c p : P2) ∈ frontier T := ⟨subset_closure (c p).property, hn⟩
    have hfp := (hc.mem_frontier_iff_of_finrank_eq rfl p).mp hfT
    have habs := (mem_frontier_squareAnnulus_iff hd (by linarith) p.property).mp hfp
    rw [hp, abs_zero] at habs
    linarith
  have hkeep' : EqOn g f (J.space \ interior T) := by simpa only [hKs] using hkeep
  have hnew' : doubleLocusOn g J.space = doubleLocusOn f (J.space \ interior T) := by
    simpa only [hKs] using hnew
  obtain ⟨hopen, hkeepOpen, hcontains⟩ :=
    reflection_open_retained_source hTC htrace hinside hkeep' hnew'
  let j : K.space → P2 := Subtype.val
  have hjrel : {v : P2 × P2 | v.1 ∈ J.space ∧ v.2 ∈ J.space ∧
      g v.1 = g v.2 ∧ v.1 ≠ v.2} =
      (fun v : K.space × K.space ↦ (j v.1, j v.2)) ''
        {v | f v.1 = f v.2 ∧ (v.1 : P2) ≠ v.2} := by
    rw [hrel]
    ext v
    constructor
    · rintro ⟨hx, hy, heq, hne⟩
      exact ⟨(⟨v.1, hx⟩, ⟨v.2, hy⟩), ⟨heq, hne⟩, rfl⟩
    · rintro ⟨⟨x, y⟩, ⟨heq, hne⟩, rfl⟩
      exact ⟨x.property, y.property, heq, hne⟩
  have hjnew : doubleLocusOn g J.space =
      j '' {x : K.space | ∃ y : K.space, f x = f y ∧ (x : P2) ≠ y} := by
    rw [hnew]
    ext x
    constructor
    · rintro ⟨hx, y, hy, heq, hne⟩
      exact ⟨⟨x, hx⟩, ⟨⟨y, hy⟩, heq, hne⟩, rfl⟩
    · rintro ⟨x, ⟨y, heq, hne⟩, rfl⟩
      exact ⟨x.property, y, y.property, heq, hne⟩
  let E := Homeomorph.setCongr M.space
  let p := E.symm.trans (M.partner.trans E)
  have hpvalue (x : doubleLocusOn f J.space) : f (p x) = f x := M.value (E.symm x)
  have hpfree (x : doubleLocusOn f J.space) : (p x : P2) ≠ x := M.free (E.symm x)
  have hpunique (x : doubleLocusOn f J.space) (y : P2) (hy : y ∈ J.space)
      (hxy : f x = f y) (hne : (x : P2) ≠ y) : y = (p x : P2) :=
    M.unique (E.symm x) y hy hne hxy
  have hG : IsCompact (doubleLocusOn f J.space) := by
    rw [← M.space]
    exact M.graph.isCompact_space_of_finite M.finite
  have hS := J.isCompact_space_of_finite hJ
  obtain ⟨hnewCompact, hnewClosed, hnewInterior, hnewUnique, hnewCross, hlocal⟩ :=
    ordinary_crossings_preserved_by_retained_copy hKS (K.isCompact_space_of_finite hK).isClosed
      hS hS hG p p.continuous hpvalue hpfree hpunique
      (double_image_interior_of_proper_rim hin hfront hcollision) hcross
      j Subtype.val_injective continuous_subtype_val (fun x ↦ hkeep x.property)
      hjrel hjnew sdiff_subset sdiff_subset hopen hopen hf.continuousOn hg.continuousOn
      (Homeomorph.refl ↥(J.space \ T)) (fun x ↦ hkeepOpen x.property) hcontains
  have hnewCollision : Disjoint (doubleLocusOn g J.space) (frontier J.space) := by
    apply disjoint_left.mpr
    intro x hx hxfront
    obtain ⟨hxK, y, hyK, hxy, hne⟩ := hnew.subset hx
    exact disjoint_left.mp hcollision ⟨hKS hxK, y, hKS hyK, hxy, hne⟩ hxfront
  have hmodel := nonempty_sourceCircleDecomposition he.compatible J hJ hg hgin hnewClosed
    hnewInterior hnewCross hnewUnique
  exact ⟨g, hg, hgin, hrim, hgfront, hnewCollision, hnewCompact, hnewCross, hlocal, hmodel,
    reflection_double_component_count_lt M i htrace hinside hnew'⟩

end PoincareConjecture.M76.Dehn.Annuli
