import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Construction.Assembly
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Contacts.PanelDepth
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Boundary.Assembly.PanelFamily
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.AnnularParameter.PanelCylinderPeriod



set_option autoImplicit false
noncomputable section
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.ProductPieces

open TubeExterior TubeExterior.CornerBands RimBands PolygonalCrossingResolution
open BoundaryAssembly

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Rim" => sphere (0 : V2) 1

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R W Q : Set X}
  {S T C D : Set P2} {f₀ f₁ : P2 → X} {j : Bool → V2 → X}






theorem exists_tube_side_base_map
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {r w : ℝ} (hw : 0 < w) (hwr : w / 2 < r)
    (P : ∀ b, OriginalDiskProduct e (R \ U.map '' openTube r) (j b))
    (HN : ((⋃ k, range (pieceBottom U P r k)) × I) ≃ₜ
      (⋃ k, range (pieceParameter U P r k)))
    (hvalue : ∀ k x t, (HN (⟨pieceBottom U P r k x,
      mem_iUnion.mpr ⟨k,mem_range_self x⟩⟩,t) : X) =
        pieceParameter U P r k (x,t))
    (b : V2 × ℝ → X)
    (hperiod : ∀ i (s : ℝ), s ∈ Icc (i.val : ℝ) (i.val + 1) →
      ∀ t ∈ I,
        b (HamiltonIndexOne.squareCircle
          ((s : ℝ) : AddCircle (4 * (2 : ℝ))),t) =
          panelFamily U (P false) (P true) r w i (s - i.val,t)) :
    ∃ rmap : (Rim : Set V2) → (⋃ k, range (pieceBottom U P r k)),
      (∀ z t, (HN (rmap z,t) : X) = b (z.1,t.1)) ∧
      (∀ x t, (HN (x,t) : X) ∈
        range (fun p : (Rim : Set V2) × I => b (p.1.1,p.2.1)) ↔
          ∃ z, rmap z = x) := by
  have hcoord (z : (Rim : Set V2)) :
      ∃ p : Fin 8 × I, ∃ hp :
          panelFamily U (P false) (P true) r w p.1 (p.2,0) ∈
            ⋃ k, range (pieceBottom U P r k),
        ∀ t : I, (HN (⟨panelFamily U (P false) (P true) r w p.1
          (p.2,0),hp⟩,t) : X) = b (z.1,t.1) := by
    letI : Fact (0 < 4 * (2 : ℝ)) := ⟨by norm_num⟩
    obtain ⟨θ,hθ⟩ := HamiltonIndexOne.squareCircle.surjective
      ⟨z.1,z.2⟩
    let s := AddCircle.equivIco (4 * (2 : ℝ)) 0 θ
    have hs : (s : ℝ) ∈ Icc (0 : ℝ) 8 := by
      exact ⟨s.property.1,by
        have hupper := s.property.2.le
        norm_num only [show (4 : ℝ) * 2 = 8 by norm_num] at hupper ⊢
        exact hupper⟩
    have hsθ : ((s : ℝ) : AddCircle (4 * (2 : ℝ))) = θ :=
      AddCircle.coe_equivIco
    obtain ⟨i,hi⟩ := mem_iUnion.mp (CyclicPanels.block_cover.symm.subset
      (show ((s : ℝ), (0 : ℝ)) ∈ Icc (0 : ℝ) 8 ×ˢ I from
        ⟨hs,by norm_num⟩))
    let x : I := ⟨(s : ℝ) - i.val,⟨by linarith [hi.1.1],by linarith [hi.1.2]⟩⟩
    obtain ⟨hp,hpvalue⟩ := panelFamily_product_value U P hw hwr HN hvalue i
      (x := (x : ℝ)) x.property
    refine ⟨(i,x),hp,?_⟩
    intro t
    change (HN (⟨panelFamily U (P false) (P true) r w i
      ((x : ℝ),0),hp⟩,t) : X) = b (z.1,t.1)
    calc
      (HN (⟨panelFamily U (P false) (P true) r w i
          ((x : ℝ),0),hp⟩,t) : X) =
          panelFamily U (P false) (P true) r w i ((x : ℝ),t.1) := hpvalue t
      _ = b (z.1,t.1) := by
        have hh := hperiod i (s : ℝ) hi.1 t t.property
        rw [hsθ,hθ] at hh
        exact hh.symm
  choose c hc using hcoord
  choose hcbase hcvalue using hc
  let rmap : (Rim : Set V2) → (⋃ k, range (pieceBottom U P r k)) :=
    fun z => ⟨panelFamily U (P false) (P true) r w (c z).1
      ((c z).2,0),hcbase z⟩
  refine ⟨rmap,?_,?_⟩
  · intro z t
    exact hcvalue z t
  · intro x t
    constructor
    · rintro ⟨p,hp⟩
      have hEq : (HN (x,t) : X) = (HN (rmap p.1,p.2) : X) := by
        calc
          (HN (x,t) : X) = b (p.1.1,p.2.1) := hp.symm
          _ = (HN (rmap p.1,p.2) : X) := (hcvalue p.1 p.2).symm
      have hsub : (x,t) = (rmap p.1,p.2) := HN.injective (Subtype.ext hEq)
      exact ⟨p.1,(congrArg Prod.fst hsub).symm⟩
    · rintro ⟨z,hzx⟩
      subst x
      exact ⟨(z,t),(hcvalue z t).symm⟩

end PoincareConjecture.M76.Dehn.Annuli.ProductPieces
