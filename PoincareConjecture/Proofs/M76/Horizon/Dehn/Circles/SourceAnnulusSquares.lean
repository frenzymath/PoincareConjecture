import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusReflection
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusCap
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SquareRimPolygon
import PoincareConjecture.Proofs.M76.Mathlib.PolygonFinitePLImage
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallNormalization

set_option autoImplicit false

open Set Geometry Metric PLAnnularStrip
open PoincareConjecture.M76.Dehn

namespace Dehn

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)

def annulusSquare (L u : ℝ) : Set P2 := Icc u (L - u) ×ˢ Icc u (L - u)

theorem mem_annulusSquare_iff (L u : ℝ) (p : P2) :
    p ∈ annulusSquare L u ↔ u ≤ depth L p := by
  simp only [annulusSquare, mem_prod, mem_Icc, depth, le_min_iff]
  constructor
  · rintro ⟨⟨hx, hx'⟩, ⟨hy, hy'⟩⟩
    exact ⟨⟨hx, hy⟩, ⟨by linarith, by linarith⟩⟩
  · rintro ⟨⟨hx, hy⟩, ⟨hx', hy'⟩⟩
    exact ⟨⟨hx, by linarith⟩, ⟨hy, by linarith⟩⟩

theorem mem_interior_annulusSquare_iff (L u : ℝ) (p : P2) :
    p ∈ interior (annulusSquare L u) ↔ u < depth L p := by
  simp only [annulusSquare, interior_prod_eq, interior_Icc, mem_prod,
    mem_Ioo, depth, lt_min_iff]
  constructor
  · rintro ⟨⟨hx, hx'⟩, ⟨hy, hy'⟩⟩
    exact ⟨⟨hx, hy⟩, ⟨by linarith, by linarith⟩⟩
  · rintro ⟨⟨hx, hy⟩, ⟨hx', hy'⟩⟩
    exact ⟨⟨hx, by linarith⟩, ⟨hy, by linarith⟩⟩

theorem mem_frontier_annulusSquare_iff (L u : ℝ) (p : P2) :
    p ∈ frontier (annulusSquare L u) ↔ depth L p = u := by
  have hc : IsClosed (annulusSquare L u) := isClosed_Icc.prod isClosed_Icc
  rw [frontier, hc.closure_eq, mem_sdiff, mem_annulusSquare_iff,
    mem_interior_annulusSquare_iff]
  exact ⟨fun h => le_antisymm (le_of_not_gt h.2) h.1, fun h => by simp [h]⟩

theorem isFinitePLBallPair_annulusSquare {L u : ℝ} (hu : 2 * u < L) :
    IsFinitePLBallPair P2 (annulusSquare L u) (frontier (annulusSquare L u)) := by
  have h := (isFinitePLBallPair_Icc (by linarith : u < L - u)).prod
    (isFinitePLBallPair_Icc (by linarith : u < L - u))
  exact (h.frontier_eq_of_finrank_eq rfl).symm ▸ h

theorem annulusSquare_partition {L d : ℝ} (hd : 0 < d) :
    annulusSquare L d ∪ squareAnnulus L d = annulusSquare L (-d) ∧
      annulusSquare L d ∩ squareAnnulus L d = frontier (annulusSquare L d) ∧
      frontier (annulusSquare L (-d)) ⊆ squareAnnulus L d := by
  refine ⟨?_, ?_, ?_⟩
  · ext p
    rw [mem_union, mem_annulusSquare_iff, mem_squareAnnulus_iff_depth,
      mem_annulusSquare_iff]
    simp only [mem_Icc]
    constructor
    · rintro (h | h)
      · linarith
      · exact h.1
    · intro h
      by_cases hp : d ≤ depth L p
      · exact Or.inl hp
      · exact Or.inr ⟨h, (lt_of_not_ge hp).le⟩
  · ext p
    rw [mem_inter_iff, mem_annulusSquare_iff, mem_squareAnnulus_iff_depth,
      mem_frontier_annulusSquare_iff]
    simp only [mem_Icc]
    constructor
    · exact fun h => le_antisymm h.2.2 h.1
    · intro h
      rw [h]
      exact ⟨le_rfl, by linarith, le_rfl⟩
  · intro p hp
    rw [mem_frontier_annulusSquare_iff] at hp
    rw [mem_squareAnnulus_iff_depth, hp]
    exact ⟨le_rfl, by linarith⟩

theorem exists_polygon_annulusSquare_frontier {L u : ℝ} (hu : 2 * u < L) :
    ∃ (n : ℕ) (P : Polygon P2 (n + 3)), P.HasSimplicialEdges ∧
      Function.Injective P ∧ P.boundary ℝ = frontier (annulusSquare L u) := by
  obtain ⟨e, he, heb⟩ := (isFinitePLBallPair_annulusSquare hu).exists_cube_chart
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
  obtain ⟨f, hf, hef⟩ := he.symm
  have hi : InjOn f (closedBall (0 : V2) 1) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (e.symm.injective (Subtype.ext
      ((hef ⟨x, hx⟩).trans (hxy.trans (hef ⟨y, hy⟩).symm))))
  have hsub : squareRimPolygon.boundary ℝ ⊆ closedBall (0 : V2) 1 := by
    rw [boundary_squareRimPolygon]
    exact sphere_subset_closedBall
  obtain ⟨n, P, hPi, hPs, hPb⟩ := squareRimPolygon.exists_polygon_finitePL_image
    hasSimplicialEdges_squareRimPolygon injective_squareRimPolygon hf hsub (hi.mono hsub)
  refine ⟨n, P, hPs, hPi, hPb.trans ?_⟩
  rw [boundary_squareRimPolygon]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← hef ⟨x, sphere_subset_closedBall hx⟩]
    apply (heb (e.symm ⟨x, sphere_subset_closedBall hx⟩)).mpr
    rw [e.apply_symm_apply, frontier_closedBall _ one_ne_zero]
    exact hx
  · intro hy
    let y' : annulusSquare L u := ⟨y, (isClosed_Icc.prod isClosed_Icc).frontier_subset hy⟩
    refine ⟨e y', ?_, ?_⟩
    · have h := (heb y').mp hy
      rwa [frontier_closedBall _ one_ne_zero] at h
    · rw [← hef, e.symm_apply_apply]

theorem exists_polygon_square_annulus_boundary {T : Set P2} {L d u : ℝ}
    (hd : 0 < d) (hwidth : 4 * d < L) (hu : u = -d ∨ u = d)
    (c : squareAnnulus L d ≃ₜ T) (hc : c.IsFinitePL) :
    ∃ (n : ℕ) (P : Polygon P2 (n + 3)), P.HasSimplicialEdges ∧
      Function.Injective P ∧
      P.boundary ℝ ⊆ T ∧
      ∀ p : squareAnnulus L d, (c p : P2) ∈ P.boundary ℝ ↔ depth L p = u := by
  obtain ⟨n, Q, hQ, hQi, hQb⟩ := exists_polygon_annulusSquare_frontier
    (L := L) (u := u) (by rcases hu with rfl | rfl <;> linarith)
  obtain ⟨f, hf, hcf⟩ := hc
  have hsub : Q.boundary ℝ ⊆ squareAnnulus L d := by
    intro p hp
    have he := (mem_frontier_annulusSquare_iff L u p).mp (hQb ▸ hp)
    rw [mem_squareAnnulus_iff_depth, he]
    rcases hu with rfl | rfl <;> constructor <;> linarith
  have hi : InjOn f (squareAnnulus L d) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (c.injective (Subtype.ext
      ((hcf ⟨x, hx⟩).trans (hxy.trans (hcf ⟨y, hy⟩).symm))))
  obtain ⟨m, P, hPi, hP, hPb⟩ := Q.exists_polygon_finitePL_image hQ hQi hf hsub (hi.mono hsub)
  refine ⟨m, P, hP, hPi, ?_, ?_⟩
  · rintro y hy
    obtain ⟨x, hx, rfl⟩ := hPb ▸ hy
    rw [← hcf ⟨x, hsub hx⟩]
    exact (c ⟨x, hsub hx⟩).property
  · intro p
    rw [hPb, hcf p]
    constructor
    · rintro ⟨x, hx, hxp⟩
      have he := hi (hsub hx) p.property hxp
      exact (mem_frontier_annulusSquare_iff L u p).mp (he ▸ (hQb ▸ hx))
    · intro hp
      exact ⟨p, hQb.symm ▸ (mem_frontier_annulusSquare_iff L u p).mpr hp, rfl⟩

end Dehn
