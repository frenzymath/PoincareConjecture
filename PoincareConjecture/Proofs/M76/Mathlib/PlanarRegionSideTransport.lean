import PoincareConjecture.Proofs.M76.Mathlib.AffinePlaneRectangleIncidence











set_option autoImplicit false

open Set




theorem IsPreconnected.mem_iff_of_disjoint_frontier
    {X : Type*} [TopologicalSpace X] {S D : Set X}
    (hS : IsPreconnected S) (hdis : Disjoint S (frontier D))
    {x y : X} (hx : x ∈ S) (hy : y ∈ S) : x ∈ D ↔ y ∈ D := by
  have hinside {z : X} (hzS : z ∈ S) (hzD : z ∈ D) : z ∈ interior D := by
    by_contra hz
    exact disjoint_left.mp hdis hzS ⟨subset_closure hzD, hz⟩
  have hfront : Disjoint (frontier (interior D)) S :=
    disjoint_left.mpr (fun _ hz hzS =>
      disjoint_left.mp hdis hzS (frontier_interior_subset hz))
  constructor
  · intro hxD
    exact interior_subset ((hS.m76_subset_of_disjoint_frontier isOpen_interior hfront
      ⟨x, hx, hinside hx hxD⟩) hy)
  · intro hyD
    exact interior_subset ((hS.m76_subset_of_disjoint_frontier isOpen_interior hfront
      ⟨y, hy, hinside hy hyD⟩) hx)

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]






theorem IsFinitePLBallPair.mem_iff_of_preconnected_avoiding_rim_in_plane
    {d q T : Set E} (hd : IsFinitePLBallPair (ℝ × ℝ) d q)
    (A : E →ᵃ[ℝ] ℝ) (hA : A.linear ≠ 0) (hdim : Module.finrank ℝ E = 3)
    (hdplane : d ⊆ {x | A x = 0})
    (hT : IsPreconnected T) (hTplane : T ⊆ {x | A x = 0})
    (havoid : Disjoint T q) {x y : E} (hx : x ∈ T) (hy : y ∈ T) :
    x ∈ d ↔ y ∈ d := by
  obtain ⟨a, R, _, hleft, _⟩ := A.exists_zeroLevel_coordinates (F := ℝ × ℝ) hA
    (by simpa [Module.finrank_prod] using hdim)
  have hR : InjOn R {x | A x = 0} := hleft.injOn
  have hdR := hd.affine_image R (hR.mono hdplane)
  have hTR : IsPreconnected (R '' T) := hT.image R R.continuous.continuousOn
  have hdis : Disjoint (R '' T) (frontier (R '' d)) := by
    rw [hdR.frontier_eq_of_finrank_eq rfl]
    apply disjoint_left.mpr
    rintro _ ⟨u, hu, rfl⟩ ⟨v, hv, heq⟩
    have hvu : v = u := hR (hdplane (hd.1 hv)) (hTplane hu) heq
    exact disjoint_left.mp havoid hu (hvu ▸ hv)
  have hmem {z : E} (hz : z ∈ T) : R z ∈ R '' d ↔ z ∈ d := by
    constructor
    · rintro ⟨v, hv, heq⟩
      have hvz : v = z := hR (hdplane hv) (hTplane hz) heq
      exact hvz ▸ hv
    · intro hzD
      exact mem_image_of_mem R hzD
  exact (hmem hx).symm.trans
    ((hTR.mem_iff_of_disjoint_frontier hdis (mem_image_of_mem R hx)
      (mem_image_of_mem R hy)).trans (hmem hy))

end Set
