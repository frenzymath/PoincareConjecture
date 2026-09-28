import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.UnionDisk.Map
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Cup.Map

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli.BoundaryCup

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_proper_disk_from_cup
    {X ι E : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {D U W : Set E} {a b : E}
    (hD : IsFinitePLBallPair P2 D (U ∪ W))
    (hU : IsFinitePLBallPair ℝ U {a, b}) (hW : IsFinitePLBallPair ℝ W {a, b})
    (hUW : U ∩ W = {a, b}) (hab : a ≠ b)
    {v f : E → X} (hv : PolyhedralPLInCharts e v D) (hf : PolyhedralPLInCharts e f D)
    (hvi : InjOn v D) (hfi : InjOn f D) (hkeep : EqOn v f W)
    (hcontact : (v '' D) ∩ (f '' D) = f '' W)
    {R : Set X} (hvR : MapsTo v D R) (hfR : MapsTo f D R)
    (hvproper : ∀ x ∈ D, v x ∈ frontier R ↔ x ∈ U)
    (hfproper : ∀ x ∈ D, f x ∈ frontier R ↔ x ∈ U) :
    ∃ g : P2 → X, PolyhedralPLInCharts e g BoundaryUnionDisk.whole ∧
      InjOn g BoundaryUnionDisk.whole ∧ MapsTo g BoundaryUnionDisk.whole R ∧
      (∀ x ∈ BoundaryUnionDisk.whole, g x ∈ frontier R ↔ x ∈ frontier BoundaryUnionDisk.whole) ∧
      g '' BoundaryUnionDisk.whole = v '' D ∪ f '' D := by
  let maps : Bool → E → X := fun i ↦ if i then f else v
  have hmaps : ∀ i, PolyhedralPLInCharts e (maps i) D := by intro i; cases i <;> assumption
  have himaps : ∀ i, InjOn (maps i) D := by intro i; cases i <;> assumption
  have hmapsR : ∀ i, MapsTo (maps i) D R := by intro i; cases i <;> assumption
  have hmapsProper : ∀ i x, x ∈ D → (maps i x ∈ frontier R ↔ x ∈ U) := by
    intro i; cases i <;> assumption
  have himage : v '' W = f '' W := image_congr hkeep
  have hcontact' : (v '' D) ∩ (f '' D) = v '' W := hcontact.trans himage.symm
  obtain ⟨g, hg, hgi, _, hgR, hgproper, hgparts, _⟩ :=
    BoundaryUnionDisk.exists_original_union_disk_map he (fun _ ↦ D) (fun _ ↦ U)
      (fun _ ↦ W) (fun _ ↦ a) (fun _ ↦ b) maps R (fun _ ↦ hD) (fun _ ↦ hU)
      (fun _ ↦ hW) (fun _ ↦ hUW) (fun _ ↦ hab) hmaps himaps himage
      (hkeep (hW.1 (by simp))) (hkeep (hW.1 (by simp))) hcontact' hmapsR hmapsProper
  refine ⟨g, hg, hgi, hgR, hgproper, ?_⟩
  rw [← BoundaryUnionDisk.half_union, image_union, hgparts false, hgparts true]
  rfl

end PoincareConjecture.M76.Dehn.Annuli.BoundaryCup
