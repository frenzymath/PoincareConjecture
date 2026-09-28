import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Construction.FromEndpointModels
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.Oriented.Tube







set_option autoImplicit false
open Poincare.Topology.Orientation.ProjectivePlane
open Set Metric Geometry Topology PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli.ProductConstruction
open TubeExterior TubeExterior.CornerBands RimBands

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "I" => Icc (0 : ℝ) 1

open Classical in
theorem exists_marked_product_of_spanning_tube_of_localOrientation
    {X ι : Type} [TopologicalSpace X] [T2Space X]
    (O : LocalOrientation X)
    (E : Bool → Type) [∀ b, NormedAddCommGroup (E b)]
    [∀ b, NormedSpace ℝ (E b)] [∀ b, FiniteDimensional ℝ (E b)]
    {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
    {C D : Set P2} {f₀ f₁ : P2 → X}
    (U : OriginalIntervalTube e R W Ann Ann C D f₀ f₁)
    (hR : IsCompact R) (hI : IsPLIrreducible e R) (hconn : IsPreconnected R)
    (hf₀ : PolyhedralPLInCharts e f₀ Ann) (hf₁ : PolyhedralPLInCharts e f₁ Ann)
    (hi₀ : InjOn f₀ Ann) (hi₁ : InjOn f₁ Ann)
    (hR₀ : MapsTo f₀ Ann R) (hR₁ : MapsTo f₁ Ann R)
    (hp₀ : ∀ z ∈ Ann, f₀ z ∈ frontier R ↔ z ∈ frontier Ann)
    (hp₁ : ∀ z ∈ Ann, f₁ z ∈ frontier R ↔ z ∈ frontier Ann)
    (houter₀ : (C ∩ {z : P2 | depth 8 z = -1}).Nonempty)
    (hinner₀ : (C ∩ {z : P2 | depth 8 z = 1}).Nonempty)
    (houter₁ : (D ∩ {z : P2 | depth 8 z = -1}).Nonempty)
    (hinner₁ : (D ∩ {z : P2 | depth 8 z = 1}).Nonempty)
    (hmeet : Ann ∩ f₀ ⁻¹' (f₁ '' Ann) = C)
    (hdistinct : connectedComponentIn (frontier R) (U.map ((0,0),0)) ≠
      connectedComponentIn (frontier R) (U.map ((0,0),1)))
    (K : ∀ b, SimplicialComplex ℝ (E b)) (hK : ∀ b, (K b).faces.Finite)
    (hpure : ∀ b, ∀ s ∈ (K b).faces, ∃ t ∈ (K b).faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ b, ∀ s ∈ (K b).faces, s.card = 2 →
      {t : Finset (E b) | t ∈ (K b).faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ b, ∀ q ∈ (K b).vertices, IsConnected ((K b).link q).space)
    (hcount : ∀ b, (K b).surfaceEulerCount = 0)
    (Hmodel : ∀ b, (K b).space ≃ₜ
      connectedComponentIn (frontier R) (U.map ((0,0),if b then 1 else 0)))
    (a : ∀ b, E b → X) (ha : ∀ b, PolyhedralPLInCharts e (a b) (K b).space)
    (hav : ∀ b, ∀ z : (K b).space, a b z = (Hmodel b z : X)) :
    let Z₀ := connectedComponentIn (frontier R) (U.map ((0,0),0))
    let Z₁ := connectedComponentIn (frontier R) (U.map ((0,0),1))
    ∃ H : (Z₀ × I) ≃ₜ R,
      (∀ x, (H (x,⟨0,by norm_num⟩) : X) = x) ∧
      range (fun x => (H (x,⟨1,by norm_num⟩) : X)) = Z₁ ∧
      (∀ x t, (H (x,t) : X) ∈ frontier R ↔ (t : ℝ) = 0 ∨ (t : ℝ) = 1) ∧
      ∃ (s : Finset R) (G : X → (s → ℝ × V3))
        (HG : ((G '' Z₀) ×ˢ I) ≃ₜ (G '' R)),
        Continuous G ∧
        (∀ i, LocallyPiecewiseAffineOn (G ∘ (e i).symm) (e i).target) ∧
        (∀ x ∈ R, ∀ y : X, G x = G y → x = y) ∧
        HG.IsFinitePL ∧ HG.symm.IsFinitePL ∧
        (∀ (x : Z₀) (t : I),
          (HG ⟨(G x,t),⟨mem_image_of_mem G x.property,t.property⟩⟩ : s → ℝ × V3) =
            G (H (x,t))) ∧
        ∀ x ∈ R, ∃ (i : ι) (V : Set X) (b : (s → ℝ × V3) →ᴬ[ℝ] V3),
          IsOpen V ∧ x ∈ V ∧ V ⊆ (e i).source ∧ EqOn (b ∘ G) (e i) V := by
  classical
  obtain ⟨k,w,ρ,P,F,_,_,_,_,_,_,_,_,_,hw,hρ,hρr,hwρ,hmark,harms,hlateral,hdis,hopen⟩ :=
    exists_original_unsigned_marked_disk_products_of_tube_of_localOrientation O U hR hI.1
      hf₀ hf₁ hi₀ hi₁ hR₀ hR₁ hp₀ hp₁ houter₀ hinner₀ houter₁ hinner₁ hmeet
  exact exists_marked_product_of_endpoint_models E U hR hI hconn hw (by norm_num)
    P F ρ hρ hρr hwρ hmark harms hlateral hdis hopen hdistinct K hK hpure hcofaces
    hlinks hcount Hmodel a ha hav

end PoincareConjecture.M76.Dehn.Annuli.ProductConstruction
