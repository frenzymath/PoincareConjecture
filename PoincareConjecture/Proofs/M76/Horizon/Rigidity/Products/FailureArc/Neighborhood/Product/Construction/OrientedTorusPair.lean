import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Construction.OrientedSourcePair
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.EndDisks.FromPLTorus



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


theorem exists_marked_product_of_torus_source_annulus_pair_of_localOrientation
    {X ι : Type} [TopologicalSpace X] [T2Space X] (O : LocalOrientation X)
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (F : Bool → Set X)
    (hR : IsCompact R) (hI : IsPLIrreducible e R) (hconn : IsPreconnected R)
    (hF : ∀ b, F b ⊆ frontier R)
    (hFdis : Disjoint (F false) (F true))
    (x : ∀ b, F b)
    (hcomponent : ∀ b, connectedComponentIn (frontier R) (x b : X) = F b)
    (period : Bool → ℝ) (hperiod : ∀ b, 0 < period b)
    (T : ∀ b, (AddCircle (period b) × AddCircle (period b)) ≃ₜ F b)
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
  classical
  let := ChartedSpace.ofChartCover e hI.1.cover
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace V3 X
  have models (b : Bool) :=
    Dehn.Annuli.ProductEndDisks.exists_original_torus_component_model_of_localOrientation
      hI.1 hR (hF b) (x b) (hcomponent b) O (hperiod b) (T b)
  choose s phi K a Hmodel hphi hphiPL hK hKconn hcount hpure hcofaces hlinks ha hav hinverse
    using models
  exact exists_marked_product_of_original_source_annulus_pair_of_localOrientation
    O (fun b => s b → ℝ × V3) F hR hI hconn hF hFdis x hcomponent
    K hK hpure hcofaces (fun b z hz => by
      convert hlinks b z hz using 1
      congr!
      congr 2
      exact Subsingleton.elim _ _)
    hcount Hmodel a ha (fun b z => (hav b z).symm)
    j hj hji hjR hjp hjmark p hpoint hboundary

end PoincareConjecture.M76
