import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.PlanarReparametrization
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Intersections.ProperAnnularRims

set_option autoImplicit false
open Set Geometry Metric Topology PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Q2" => sphere (0 : V2) 1

theorem exists_planar_spanning_pair_with_marked_intersection
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (F : Bool → Set X) (hF : ∀ b, F b ⊆ frontier R)
    (hdis : Disjoint (F false) (F true))
    (j : Bool → (V1 × V2) → X)
    (hj : ∀ b, PolyhedralPLInCharts e (j b) source)
    (hji : ∀ b, IsEmbedding (fun x : source => j b x))
    (hjR : ∀ b, MapsTo (j b) source R)
    (hproper : ∀ b (x : source), j b x ∈ frontier R ↔
      (x : V1 × V2).1 ∈ sphere (0 : V1) 1)
    (hmark : ∀ b c (z : Q2), j b (endpoint c, z) ∈ F c)
    (p : X) (hpoint : (j false '' source ∩ j true '' source) ∩ F false = {p}) :
    ∃ g : Bool → (ℝ × ℝ) → X,
      (∀ b, PolyhedralPLInCharts e (g b) Ann) ∧
      (∀ b, InjOn (g b) Ann) ∧
      (∀ b, MapsTo (g b) Ann R) ∧
      (∀ b (x : Ann), g b x ∈ frontier R ↔ depth 8 x = -1 ∨ depth 8 x = 1) ∧
      (∀ b (x : Ann), g b x ∈ F false ↔ depth 8 x = -1) ∧
      (∀ b (x : Ann), depth 8 x = 1 → g b x ∈ F true) ∧
      (∀ b, g b '' Ann = j b '' source) ∧
      (g false '' Ann ∩ g true '' Ann) ∩ F false = {p} := by
  obtain ⟨K, _, hKs⟩ := exists_source_triangulation
  have hdata (b : Bool) := exists_marked_planar_annulus_reparametrization
    (F := F) K hKs (hKs.symm ▸ hj b)
    ((hji b).comp (Homeomorph.setCongr hKs).isEmbedding)
    (fun x hx => hjR b (hKs.subset hx))
    (fun x => hproper b ⟨x, hKs.subset x.property⟩) (hmark b)
  choose period H g hH hHi hvalue hrim hg hgi hgR hgp hgm himage using hdata
  have himage (b : Bool) : g b '' Ann = j b '' source := by
    simpa only [hKs] using himage b
  have hlast (b : Bool) (x : Ann) (hx : depth 8 x = 1) : g b x ∈ F true := by
    have hm : x ∈ range (annulusRimPoint true) := by
      rw [range_annulusRimPoint]
      exact hx
    obtain ⟨z, rfl⟩ := hm
    exact hgm b true z
  refine ⟨g, hg, ?_, hgR, hgp, ?_, hlast, himage, ?_⟩
  · intro b x hx y hy hxy
    exact congrArg Subtype.val ((hgi b).injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  · intro b x
    constructor
    · intro hx
      rcases (hgp b x).mp (hF false hx) with hd | hd
      · exact hd
      · exact (disjoint_left.mp hdis hx (hlast b x hd)).elim
    · intro hx
      have hm : x ∈ range (annulusRimPoint false) := by
        rw [range_annulusRimPoint]
        exact hx
      obtain ⟨z, rfl⟩ := hm
      exact hgm b false z
  · rw [himage false, himage true]
    exact hpoint

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
