import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskTriangulation
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskInteriorCharts
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskBoundaryCharts

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_proper_disk_pair_chart {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {R D : Set E} (a : E ≃ᴬ[ℝ] V3)
    (hDomainA : PLDomain
      (fun _ : Unit => (Homeomorph.refl V3).toOpenPartialHomeomorph) (a '' R))
    (hDR : D ⊆ R)
    (b : closedBall (0 : V2) 1 ≃ₜ D) (hb : b.IsFinitePL)
    (hproper : ∀ x : closedBall (0 : V2) 1,
      (b x : E) ∈ frontier R ↔ (x : V2) ∈ sphere (0 : V2) 1)
    {p : E} (hpD : p ∈ D) :
    ∃ C : HamiltonProperDiskPairChart R D, p ∈ C.chart.source := by
  classical
  have himage (S : Set E) (x : E) : a x ∈ a '' S ↔ x ∈ S := by
    constructor
    · rintro ⟨y, hy, heq⟩
      exact a.injective heq ▸ hy
    · exact mem_image_of_mem a
  have hfront : a '' frontier R = frontier (a '' R) :=
    a.toHomeomorph.image_frontier R
  let bA : closedBall (0 : V2) 1 ≃ₜ (a '' D) := b.trans (a.toHomeomorph.image D)
  have hbA : bA.IsFinitePL := by
    obtain ⟨f, hf, hbf⟩ := hb
    exact ⟨fun x => a (f x), hf.postcomp a.toContinuousAffineMap,
      fun x => congrArg a (hbf x)⟩
  have hproperA (x : closedBall (0 : V2) 1) :
      (bA x : V3) ∈ frontier (a '' R) ↔ (x : V2) ∈ sphere (0 : V2) 1 := by
    change a (b x : E) ∈ frontier (a '' R) ↔ _
    rw [← hfront, himage]
    exact hproper x
  have hpA : a p ∈ a '' D := mem_image_of_mem a hpD
  obtain ⟨C, hpC⟩ : ∃ C : HamiltonProperDiskPairChart (a '' R) (a '' D),
      a p ∈ C.chart.source := by
    by_cases hpfront : p ∈ frontier R
    · have hpfrontA : a p ∈ frontier (a '' R) :=
        hfront.subset (mem_image_of_mem a hpfront)
      obtain ⟨H, hpH, _, hH, hHi, _, hHR, hHD⟩ :=
        exists_proper_disk_boundary_pair_chart hDomainA (image_mono hDR)
          bA hbA hproperA hpA hpfrontA
      exact ⟨⟨H, hH, hHi, Or.inr ⟨hHR, hHD⟩⟩, hpH⟩
    · have hpint : p ∈ interior R := by
        by_contra hn
        exact hpfront ⟨subset_closure (hDR hpD), hn⟩
      have hpintA : a p ∈ interior (a '' R) := by
        change a.toHomeomorph p ∈ interior (a.toHomeomorph '' R)
        rw [← a.toHomeomorph.image_interior]
        exact mem_image_of_mem a hpint
      obtain ⟨H, hpH, hHR, _, hH, hHi, _, hHD⟩ :=
        exists_proper_disk_interior_pair_chart (by simp) bA hbA hproperA hpA hpintA
      exact ⟨⟨H, hH, hHi, Or.inl ⟨hHR, hHD⟩⟩, hpH⟩
  let H := a.toHomeomorph.toOpenPartialHomeomorph.trans C.chart
  have hH : LocallyPiecewiseAffineOn H H.source :=
    C.piecewiseAffine.comp
      (locallyPiecewiseAffineOn_affine a.toContinuousAffineMap isOpen_univ)
  have hHi : LocallyPiecewiseAffineOn H.symm H.target :=
    (locallyPiecewiseAffineOn_affine a.symm.toContinuousAffineMap isOpen_univ).comp
      C.inverse_piecewiseAffine
  have hmodel :
      (H.source ⊆ interior R ∧ ∀ x ∈ H.source, x ∈ D ↔ (H x).2 = 0) ∨
      ((∀ x ∈ H.source, x ∈ R ↔ 0 ≤ (H x).1.1) ∧
        ∀ x ∈ H.source, x ∈ D ↔ 0 ≤ (H x).1.1 ∧ (H x).2 = 0) := by
    rcases C.model with ⟨hsource, hplane⟩ | ⟨hregion, hdisk⟩
    · left
      constructor
      · intro x hx
        have hax := hsource hx.2
        change a.toHomeomorph x ∈ interior (a.toHomeomorph '' R) at hax
        rw [← a.toHomeomorph.image_interior] at hax
        exact (himage (interior R) x).mp hax
      · intro x hx
        exact (himage D x).symm.trans (hplane (a x) hx.2)
    · right
      exact ⟨fun x hx => (himage R x).symm.trans (hregion (a x) hx.2),
        fun x hx => (himage D x).symm.trans (hdisk (a x) hx.2)⟩
  exact ⟨⟨H, hH, hHi, hmodel⟩, ⟨mem_univ p, hpC⟩⟩

end PoincareConjecture.M76.HamiltonIndexOne
