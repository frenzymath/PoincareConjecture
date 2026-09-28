import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Annuli.NestedPolygonAnnulus
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Annuli.CollarAnnulusLift

set_option autoImplicit false

open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

open _root_.Dehn

local notation "P2" => (ℝ × ℝ)

theorem annulusDepthImage_eq_of_iff
    {E : Type*} [NormedAddCommGroup E] {A B : Set E}
    (a : squareAnnulus 8 1 ≃ₜ A) (u : ℝ) (hB : B ⊆ A)
    (hlevel : ∀ p : squareAnnulus 8 1, depth 8 (p : P2) = u ↔ (a p : E) ∈ B) :
    annulusDepthImage a u = B := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (hlevel p).mp hp
  · intro hx
    let p := a.symm ⟨x, hB hx⟩
    have hp : (a p : E) = x := congrArg Subtype.val (a.apply_symm_apply ⟨x, hB hx⟩)
    exact ⟨p, (hlevel p).mpr (hp.symm ▸ hx), hp⟩

theorem exists_essential_polygon_annuli
    {n : ℕ} (P : Polygon P2 (n + 3))
    (hP : P.HasSimplicialEdges) (hi : Function.Injective P)
    {L d : ℝ} (hd : 0 < d) (hwidth : 4 * d < L)
    (hinner : annulusSquare L d ⊆ P.inside)
    (houter : closure P.inside ⊆ interior (annulusSquare L (-d))) :
    ∃ (a₀ : squareAnnulus 8 1 ≃ₜ (annulusSquare L (-d) \ P.inside : Set P2))
      (a₁ : squareAnnulus 8 1 ≃ₜ
        (annulusSquare L (-d) \ interior (annulusSquare L 0) : Set P2)),
      a₀.IsFinitePL ∧ a₁.IsFinitePL ∧
      annulusSquare L (-d) \ P.inside ⊆ squareAnnulus L d ∧
      annulusSquare L (-d) \ interior (annulusSquare L 0) ⊆ squareAnnulus L d ∧
      annulusDepthImage a₀ 1 = P.boundary ℝ ∧
      annulusDepthImage a₁ 1 = frontier (annulusSquare L 0) ∧
      annulusDepthImage a₀ (-1) = frontier (annulusSquare L (-d)) ∧
      annulusDepthImage a₁ (-1) = frontier (annulusSquare L (-d)) := by
  have hPdisk : IsFinitePLBallPair P2 (closure P.inside)
      (frontier (closure P.inside)) := by
    rw [P.frontier_closure_inside hP hi]
    exact P.isFinitePLBallPair_closed_inside hP hi
  have hOdisk := isFinitePLBallPair_annulusSquare (L := L) (u := -d)
    (show 2 * (-d) < L by linarith)
  have hMdisk := isFinitePLBallPair_annulusSquare (L := L) (u := 0)
    (show 2 * 0 < L by linarith)
  have hMO : annulusSquare L 0 ⊆ interior (annulusSquare L (-d)) := by
    intro x hx
    rw [mem_interior_annulusSquare_iff]
    have hh := (mem_annulusSquare_iff L 0 x).mp hx
    linarith
  obtain ⟨b₀, hb₀, ho₀, hi₀⟩ := exists_square_annulus_nested_disks hPdisk hOdisk houter
    (L := 8) (d := 1) (by norm_num) (by norm_num)
  obtain ⟨a₁, ha₁, ho₁, hi₁⟩ := exists_square_annulus_nested_disks hMdisk hOdisk hMO
    (L := 8) (d := 1) (by norm_num) (by norm_num)
  have hcarrier : annulusSquare L (-d) \ interior (closure P.inside) =
      annulusSquare L (-d) \ P.inside := by rw [P.interior_closure_inside hP hi]
  let a₀ := b₀.trans (Homeomorph.setCongr hcarrier)
  have ha₀ : a₀.IsFinitePL := by
    obtain ⟨f, hf, hval⟩ := hb₀
    exact ⟨f, hf, hval⟩
  have hPbound : P.boundary ℝ ⊆ annulusSquare L (-d) \ P.inside := by
    intro x hx
    have hc : x ∈ closure P.inside := by
      rw [← P.frontier_inside hP hi] at hx
      exact frontier_subset_closure hx
    refine ⟨interior_subset (houter hc), ?_⟩
    have hf : x ∈ frontier P.inside := (P.frontier_inside hP hi).symm ▸ hx
    rw [frontier, (P.isOpen_inside hP hi).interior_eq] at hf
    exact hf.2
  have hObound₀ : frontier (annulusSquare L (-d)) ⊆
      annulusSquare L (-d) \ P.inside := by
    intro x hx
    have he := (mem_frontier_annulusSquare_iff L (-d) x).mp hx
    refine ⟨(mem_annulusSquare_iff L (-d) x).mpr he.ge, ?_⟩
    intro hp
    have hh := (mem_interior_annulusSquare_iff L (-d) x).mp
      (houter (subset_closure hp))
    linarith
  have hMbound : frontier (annulusSquare L 0) ⊆
      annulusSquare L (-d) \ interior (annulusSquare L 0) := by
    intro x hx
    have he := (mem_frontier_annulusSquare_iff L 0 x).mp hx
    refine ⟨(mem_annulusSquare_iff L (-d) x).mpr (by linarith), ?_⟩
    rw [mem_interior_annulusSquare_iff, he]
    exact lt_irrefl _
  have hObound₁ : frontier (annulusSquare L (-d)) ⊆
      annulusSquare L (-d) \ interior (annulusSquare L 0) := by
    intro x hx
    have he := (mem_frontier_annulusSquare_iff L (-d) x).mp hx
    refine ⟨(mem_annulusSquare_iff L (-d) x).mpr he.ge, ?_⟩
    rw [mem_interior_annulusSquare_iff, he]
    linarith
  refine ⟨a₀, a₁, ha₀, ha₁, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    apply mem_squareAnnulus_iff_depth.mpr
    refine ⟨(mem_annulusSquare_iff L (-d) x).mp hx.1, ?_⟩
    exact (lt_of_not_ge (fun hh ↦ hx.2 (hinner
      ((mem_annulusSquare_iff L d x).mpr hh)))).le
  · intro x hx
    apply mem_squareAnnulus_iff_depth.mpr
    refine ⟨(mem_annulusSquare_iff L (-d) x).mp hx.1, ?_⟩
    have hh : depth L x ≤ 0 := le_of_not_gt (fun hh ↦ hx.2
      ((mem_interior_annulusSquare_iff L 0 x).mpr hh))
    linarith
  · apply annulusDepthImage_eq_of_iff a₀ 1 hPbound
    intro p
    change depth 8 (p : P2) = 1 ↔ (b₀ p : P2) ∈ P.boundary ℝ
    simpa only [P.frontier_closure_inside hP hi] using hi₀ p
  · exact annulusDepthImage_eq_of_iff a₁ 1 hMbound hi₁
  · exact annulusDepthImage_eq_of_iff a₀ (-1) hObound₀ ho₀
  · exact annulusDepthImage_eq_of_iff a₁ (-1) hObound₁ ho₁

end PoincareConjecture.M76.Dehn
