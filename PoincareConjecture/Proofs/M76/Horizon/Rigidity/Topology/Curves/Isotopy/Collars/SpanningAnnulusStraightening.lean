import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Collars.AnnularStraightening
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Collars.EmbeddedMapTransport
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.OriginalAnnularDegree



set_option autoImplicit false
open Set Geometry Metric Topology PLAnnularStrip

namespace PoincareConjecture.M76.CollarIsotopy

open PoincareConjecture.M76.Dehn PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "I" => unitInterval
local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q2" => sphere (0 : V2) 1
local notation "Ann" => squareAnnulus 8 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))

theorem exists_original_spanning_annulus_core_straightening
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R U B : Set X}
    (he : PLDomain e R) (hR : IsCompact R) (hne : (interior R).Nonempty)
    (hU : IsOpen U) (hBU : frontier R ⊆ U)
    (A : Ann ≃ₜ B) (hBS : B ⊆ frontier R) (hB : IsClosed B)
    (j : (ℝ × ℝ) → X) (hj : PolyhedralPLInCharts e j Ann)
    (hjval : ∀ z : Ann, j z = (A z : X))
    (hopen : IsOpen ((Subtype.val : frontier R → X) ⁻¹' originalAnnulusOpenMark A))
    (g : (V1 × V2) → X) (original : C(source, R))
    (hg : PolyhedralPLInCharts e g source)
    (hemb : IsEmbedding (fun x : source => g x))
    (hvalue : ∀ x : source, g x = (original x : X))
    (hproper : ∀ x : source, g x ∈ frontier R ↔ (x : V1 × V2).1 ∈ sphere (0 : V1) 1)
    (hessential : ∀ b, ¬ (sourceAnnulusRim original b).Nullhomotopic)
    (hmark : ∀ z : Q2, g (endpoint false, z) ∈ originalAnnulusOpenMark A)
    (hother : ∀ z : Q2, g (endpoint true, z) ∉ originalAnnulusOpenMark A) :
    ∃ (G : I → R ≃ₜ R) (q : Q2 ≃ₜ Circle)
        (g' : (V1 × V2) → X) (moved : C(source, R)),
      Continuous (fun z : I × R => G z.1 z.2) ∧
      Continuous (fun z : I × R => (G z.1).symm z.2) ∧ G 0 = Homeomorph.refl R ∧
      (∀ t : I, ChartwisePLHomeomorph e e (G t)) ∧
      (∀ (t : I) (x : R), (G t x : X) ∈ frontier R ↔ (x : X) ∈ frontier R) ∧
      PolyhedralPLInCharts e g' source ∧ IsEmbedding (fun x : source => g' x) ∧
      moved = (⟨G 1, (G 1).continuous⟩ : C(R, R)).comp original ∧
      (∀ x : source, g' x = (moved x : X)) ∧
      (∀ x : source, g' x ∈ frontier R ↔ (x : V1 × V2).1 ∈ sphere (0 : V1) 1) ∧
      (∀ b, ¬ (sourceAnnulusRim moved b).Nullhomotopic) ∧
      (∀ z : Q2, g' (endpoint false, z) = A (annulusCoreCircle (q z))) ∧
      sourceAnnulusRim moved true = sourceAnnulusRim original true ∧
      (∀ (t : I) (z : Q2), G t (sourceAnnulusRim original true z) =
        sourceAnnulusRim original true z) ∧
      (∀ (t : I) (x : R), (x : X) ∉ U → G t x = x) ∧
      (∀ (t : I) (x : R), (x : X) ∈ frontier R →
        (x : X) ∉ originalAnnulusOpenMark A → G t x = x) := by
  have hrim (b : Bool) (z : Q2) :
      (sourceAnnulusRim original b z : X) = g (endpoint b, z) :=
    (hvalue ⟨(endpoint b, z), sphere_subset_closedBall (endpoint_mem_sphere b), z.property⟩).symm
  let gamma : C(Q2, B) :=
    ⟨fun z => ⟨sourceAnnulusRim original false z,
      originalAnnulusOpenMark_subset A (by rw [hrim]; exact hmark z)⟩,
      (continuous_subtype_val.comp (sourceAnnulusRim original false).continuous).subtype_mk _⟩
  have horiginal : Function.Injective original := by
    intro x y hxy
    apply hemb.injective
    change g x = g y
    rw [hvalue x, hvalue y, hxy]
  have hinj : Function.Injective gamma := by
    intro x y hxy
    have h : sourceAnnulusRim original false x = sourceAnnulusRim original false y :=
      Subtype.ext (congrArg (fun z : B => (z : X)) hxy)
    exact Subtype.ext (congrArg (fun z : source => (z : V1 × V2).2) (horiginal h))
  let K := squareRimPolygon.simplicialComplex hasSimplicialEdges_squareRimPolygon
  have hK : K.faces.Finite :=
    squareRimPolygon.finite_simplicialComplex_faces hasSimplicialEdges_squareRimPolygon
  have hKs : K.space = Q2 :=
    (squareRimPolygon.simplicialComplex_space hasSimplicialEdges_squareRimPolygon).trans
      boundary_squareRimPolygon
  let p : V2 →ᴬ[ℝ] (V1 × V2) :=
    (ContinuousAffineMap.const ℝ V2 (endpoint false)).prod (ContinuousAffineMap.id ℝ V2)
  have hp : FinitePiecewiseAffineOn p K.space :=
    (K.affineOnFaces_affine p).finitePiecewiseAffineOn hK
  have hmaps : MapsTo p K.space source := by
    intro z hz
    exact ⟨sphere_subset_closedBall (endpoint_mem_sphere false), hKs ▸ hz⟩
  have hgr : PolyhedralPLInCharts e (fun z : V2 => g (endpoint false, z)) Q2 := by
    have h := hg.comp_finitePiecewiseAffineOn K hK hp hmaps
    change PolyhedralPLInCharts e (fun z => g (endpoint false, z)) K.space at h
    exact hKs ▸ h
  have hgammaVal (z : Q2) : g (endpoint false, z) = (gamma z : X) := (hrim false z).symm
  have hgammaEssential : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (squareRimLoop.map
        (((ContinuousMap.inclusion (hBS.trans he.closed.frontier_subset)).comp gamma).continuous))) ≠ 1 := by
    exact squareRimLoop_class_ne_one_of_not_nullhomotopic
      (sourceAnnulusRim original false) (hessential false)
  obtain ⟨G, q, hGc, hGci, hG0, hGPL, hfront, hpoint, _, hout, hoff⟩ :=
    exists_original_annular_circle_collar_straightening he hR hne hU hBU
      A hBS hB j hj hjval hopen gamma hinj (fun z => g (endpoint false, z)) hgr hgammaVal
      (fun z => (mem_originalAnnulusOpenMark_iff A (gamma z)).mp
        (by rw [← hgammaVal]; exact hmark z)) hgammaEssential
  have htrue (t : I) (z : Q2) :
      G t (sourceAnnulusRim original true z) = sourceAnnulusRim original true z := by
    apply hoff
    · rw [hrim]
      exact (hproper ⟨(endpoint true, z),
        sphere_subset_closedBall (endpoint_mem_sphere true), z.property⟩).mpr
          (endpoint_mem_sphere true)
    · rw [hrim]
      exact hother z
  obtain ⟨g', moved, hg', hemb', hmoved, hvalue', hproper', hessential', _, hrims, hv⟩ :=
    exists_original_embedded_cylinder_transport (G 1) (hGPL 1) (hfront 1)
      g original hg hemb hvalue hproper hessential
  refine ⟨G, q, g', moved, hGc, hGci, hG0, hGPL, hfront,
    hg', hemb', hmoved, hvalue', hproper', hessential', ?_, hrims true (htrue 1),
    htrue, hout, hoff⟩
  intro z
  rw [hv]
  exact hpoint z

end PoincareConjecture.M76.CollarIsotopy
