import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Collars.SourceAlternatives
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Resolution.BoundaryCorrespondence
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusComplement










set_option autoImplicit false

open Set Geometry PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)

theorem exists_nested_contractible_source
    (J : SimplicialComplex ℝ P2) (hJ : J.faces.Finite)
    {A₀ A₁ : Set P2} {L d : ℝ}
    (B₀ : OrientedPolygonCollar L d A₀) (B₁ : OrientedPolygonCollar L d A₁)
    (hcontract : closure B₀.outer.inside ⊆ interior J.space)
    (hnest : closure B₁.outer.inside ⊆ B₀.inner.inside) :
    ∃ (eb : B₁.inner.boundary ℝ ≃ₜ B₀.inner.boundary ℝ)
      (H : closure B₁.inner.inside ≃ₜ closure B₀.inner.inside)
      (copy : P2 → P2) (O : SimplicialComplex ℝ P2),
      eb.IsFinitePL ∧ H.IsFinitePL ∧
      FinitePiecewiseAffineOn copy (closure B₁.inner.inside) ∧
      (∀ x : closure B₁.inner.inside, copy x = (H x : P2)) ∧
      (∀ x : B₁.inner.boundary ℝ, copy x = (eb x : P2)) ∧
      (∀ x : closure B₁.inner.inside,
        copy x ∈ B₀.inner.boundary ℝ ↔ (x : P2) ∈ B₁.inner.boundary ℝ) ∧
      (∀ (p : squareAnnulus L d) (_hp : depth L p = d),
        copy (B₁.chart p) = B₀.chart p) ∧
      copy '' closure B₁.inner.inside = closure B₀.inner.inside ∧
      O.faces.Finite ∧ O.space = J.space \ B₀.outer.inside ∧
      (closure B₀.inner.inside ∪ A₀) ∪ O.space = J.space ∧
      closure B₀.inner.inside ∩ A₀ = B₀.inner.boundary ℝ ∧
      A₀ ∩ O.space = B₀.outer.boundary ℝ ∧
      Disjoint (closure B₀.inner.inside) O.space ∧
      closure B₁.inner.inside ⊆ J.space ∧
      frontier J.space ⊆ O.space := by
  have hb₀ := oriented_collar_boundary_subsets B₀
  have hb₁ := oriented_collar_boundary_subsets B₁
  obtain ⟨eb, heb, _, _, hperiod⟩ := exists_synchronized_collar_boundary_homeomorph
    B₁.inner B₀.inner B₁.inner_simplicial B₁.inner_injective hb₁.2 hb₀.2
    B₁.chart B₀.chart B₁.chart_PL B₀.chart_PL B₁.inner_depth B₀.inner_depth
  have hI := B₀.inner.isFinitePLBallPair_closed_inside B₀.inner_simplicial B₀.inner_injective
  have hQ := B₁.inner.isFinitePLBallPair_closed_inside B₁.inner_simplicial B₁.inner_injective
  have hP := B₀.outer.isFinitePLBallPair_closed_inside B₀.outer_simplicial B₀.outer_injective
  obtain ⟨H, hH, hHb, hHmem⟩ := hQ.exists_extension hI eb heb
  obtain ⟨copy, hcopy, hcopyval⟩ := hH
  have hcopyeq (x : closure B₁.inner.inside) : copy x = (H x : P2) := (hcopyval x).symm
  have hcopyb (x : B₁.inner.boundary ℝ) : copy x = (eb x : P2) := by
    have h := congrArg Subtype.val (hHb x)
    rwa [hcopyval] at h
  have himage : copy '' closure B₁.inner.inside = closure B₀.inner.inside := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hcopyeq ⟨y, hy⟩]
      exact (H ⟨y, hy⟩).property
    · intro hx
      exact ⟨H.symm ⟨x, hx⟩, (H.symm ⟨x, hx⟩).property,
        (hcopyeq _).trans (congrArg Subtype.val (H.apply_symm_apply _))⟩
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨P, hPf, hPs, _⟩, _⟩, _⟩ := hP
  obtain ⟨O, hO, hOs, hcover, hseam⟩ := exists_finite_interior_carrier_complement
    J P hJ hPf (hPs.subset.trans hcontract)
  have hPint : interior (closure B₀.outer.inside) = B₀.outer.inside :=
    B₀.outer.interior_closure_inside B₀.outer_simplicial B₀.outer_injective
  have hOspace : O.space = J.space \ B₀.outer.inside := by
    rw [hOs, hPs, hPint]
  have hPsub : closure B₀.outer.inside ⊆ J.space := hcontract.trans interior_subset
  have hIsub : closure B₀.inner.inside ⊆ closure B₀.outer.inside :=
    B₀.nested.trans subset_closure
  have hIQ : closure B₁.inner.inside ⊆ B₀.inner.inside :=
    B₁.nested.trans (subset_closure.trans hnest)
  have hIunion : closure B₀.inner.inside ∪ A₀ = closure B₀.outer.inside := by
    conv_lhs => rhs; rw [B₀.carrier]
    ext x
    constructor
    · rintro (hx | hx)
      exacts [hIsub hx, hx.1]
    · intro hx
      by_cases hi : x ∈ B₀.inner.inside
      · exact Or.inl (subset_closure hi)
      · exact Or.inr ⟨hx, hi⟩
  have hIseam : closure B₀.inner.inside ∩ A₀ = B₀.inner.boundary ℝ := by
    conv_lhs => rhs; rw [B₀.carrier]
    rw [← B₀.inner.frontier_inside B₀.inner_simplicial B₀.inner_injective,
      frontier, (B₀.inner.isOpen_inside B₀.inner_simplicial B₀.inner_injective).interior_eq]
    ext x
    exact ⟨fun hx ↦ ⟨hx.1, hx.2.2⟩, fun hx ↦ ⟨hx.1, hIsub hx.1, hx.2⟩⟩
  have hPseam : A₀ ∩ O.space = B₀.outer.boundary ℝ := by
    conv_lhs => lhs; rw [B₀.carrier]
    rw [hOspace,
      ← B₀.outer.frontier_inside B₀.outer_simplicial B₀.outer_injective,
      frontier, (B₀.outer.isOpen_inside B₀.outer_simplicial B₀.outer_injective).interior_eq]
    ext x
    constructor
    · intro hx
      exact ⟨hx.1.1, hx.2.2⟩
    · intro hx
      exact ⟨⟨hx.1, fun hi ↦ hx.2 (B₀.nested (subset_closure hi))⟩, hPsub hx.1, hx.2⟩
  refine ⟨eb, H, copy, O, heb, ⟨copy, hcopy, hcopyval⟩, hcopy, hcopyeq, hcopyb, ?_, ?_,
    himage, hO, hOspace, ?_, hIseam, hPseam, ?_,
    hIQ.trans (subset_closure.trans (hIsub.trans hPsub)), ?_⟩
  · intro x
    rw [hcopyeq x]
    exact (hHmem x).symm
  · intro p hp
    exact (hcopyb ⟨B₁.chart p, (B₁.inner_depth p).mpr hp⟩).trans (hperiod p hp)
  · rw [hIunion, ← hPs, union_comm]
    exact hcover
  · rw [hOspace]
    exact disjoint_left.mpr fun x hx hy ↦ hy.2 (B₀.nested hx)
  · intro x hx
    rw [hOspace]
    exact ⟨(J.isCompact_space_of_finite hJ).isClosed.frontier_subset hx,
      fun hp ↦ hx.2 (hcontract (subset_closure hp))⟩

end PoincareConjecture.M76.Dehn.Annuli
