import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Whole.FromSourceAnnuli
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Construction.OrientedReducedPair
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.FrontierComponents.BoundaryLocalConnectedness



set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76

open PoincareConjecture.M76.Dehn.ProtectedAnnulus
open Poincare.Topology.Orientation.ProjectivePlane

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Q" => sphere (0 : V2) 1

open Classical in


theorem exists_marked_product_of_original_source_annulus_pair_of_localOrientation
    {X ι : Type} [TopologicalSpace X] [T2Space X] (O : LocalOrientation X)
    (E : Bool → Type) [∀ b, NormedAddCommGroup (E b)]
    [∀ b, NormedSpace ℝ (E b)] [∀ b, FiniteDimensional ℝ (E b)]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (F : Bool → Set X)
    (hR : IsCompact R) (hI : IsPLIrreducible e R) (hconn : IsPreconnected R)
    (hF : ∀ b, F b ⊆ frontier R)
    (hFdis : Disjoint (F false) (F true))
    (x : ∀ b, F b)
    (hcomponent : ∀ b, connectedComponentIn (frontier R) (x b : X) = F b)
    (K : ∀ b, SimplicialComplex ℝ (E b)) (hK : ∀ b, (K b).faces.Finite)
    (hpure : ∀ b, ∀ s ∈ (K b).faces, ∃ t ∈ (K b).faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ b, ∀ s ∈ (K b).faces, s.card = 2 →
      {t : Finset (E b) | t ∈ (K b).faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ b, ∀ q ∈ (K b).vertices, IsConnected ((K b).link q).space)
    (hcount : ∀ b, (K b).surfaceEulerCount = 0)
    (Hmodel : ∀ b, (K b).space ≃ₜ F b)
    (a : ∀ b, E b → X) (ha : ∀ b, PolyhedralPLInCharts e (a b) (K b).space)
    (hav : ∀ b, ∀ z : (K b).space, a b z = (Hmodel b z : X))
    (j : Bool → V1 × V2 → X)
    (hj : ∀ b, PolyhedralPLInCharts e (j b) source)
    (hji : ∀ b, InjOn (j b) source) (hjR : ∀ b, MapsTo (j b) source R)
    (hjp : ∀ b (z : source), j b z ∈ frontier R ↔ (z : V1 × V2).1 ∈ sphere (0 : V1) 1)
    (hjmark : ∀ b c (z : Q), j b (endpoint c, z) ∈ F c)
    (p : X) (hpoint : ((j false '' source) ∩ (j true '' source)) ∩ F false = {p})
    (hboundary : ∀ y ∈ (j false '' source) ∩ (j true '' source), y ∈ frontier R →
      ∃ B : OriginalSurfacePairChart e (j false '' source) (j true '' source) y true,
        ∀ z ∈ B.coordinates.source, B.chart.symm z ∈ R ↔ 0 ≤ (B.coordinates z).1.2) :
    ∃ H : ((F false) × I) ≃ₜ R,
      (∀ x, (H (x,⟨0,by norm_num⟩) : X) = x) ∧
      range (fun x => (H (x,⟨1,by norm_num⟩) : X)) = F true ∧
      (∀ x t, (H (x,t) : X) ∈ frontier R ↔ (t : ℝ) = 0 ∨ (t : ℝ) = 1) ∧
      ∃ (s : Finset R) (G : X → (s → ℝ × V3))
        (HG : ((G '' F false) ×ˢ I) ≃ₜ (G '' R)),
        Continuous G ∧
        (∀ i, LocallyPiecewiseAffineOn (G ∘ (e i).symm) (e i).target) ∧
        (∀ x ∈ R, ∀ y : X, G x = G y → x = y) ∧
        HG.IsFinitePL ∧ HG.symm.IsFinitePL ∧
        (∀ (x : F false) (t : I),
          (HG ⟨(G x,t),⟨mem_image_of_mem G x.property,t.property⟩⟩ : s → ℝ × V3) =
            G (H (x,t))) ∧
        ∀ x ∈ R, ∃ (i : ι) (V : Set X) (b : (s → ℝ × V3) →ᴬ[ℝ] V3),
          IsOpen V ∧ x ∈ V ∧ V ⊆ (e i).source ∧ EqOn (b ∘ G) (e i) V := by
  have hcomponents (b : Bool) (y : X) (hy : y ∈ F b) :
      connectedComponentIn (frontier R) y = F b := by
    have hyc : y ∈ connectedComponentIn (frontier R) (x b : X) :=
      (hcomponent b).symm ▸ hy
    exact (connectedComponentIn_eq hyc).symm.trans (hcomponent b)
  obtain ⟨f, g, q, hf, hg, hfi, hgi, hfR, hgR, hfp, hgp, hfm, hgm,
      hfl, hgl, hq, hboundary', hinterior⟩ :=
    exists_original_positioned_planar_spanning_pair F hF hFdis hcomponents
      hI.1.cover hI.1.compatible j hj hji hjR hjp hjmark p hpoint hboundary
  exact Dehn.Annuli.ProductConstruction.exists_marked_product_of_positioned_annulus_pair_of_localOrientation
    O E F hR hI hconn hF
    (hI.1.isOpen_preimage_frontier_component hR (hF true (x true).property) (hcomponent true))
    hFdis hcomponents K hK hpure hcofaces hlinks hcount Hmodel a ha hav
    hf hg hfi hgi hfR hgR hfp hgp hfm hgm hfl hgl q hq hboundary' hinterior

end PoincareConjecture.M76
