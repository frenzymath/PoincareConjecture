import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.AnnularParameter.PanelBase
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Gluing.FinalBallAnnulusTransport
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Gluing.AttachedCollision
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.AnnularParameter.PairCylinder
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Boundary.Assembly.PanelFamily



set_option autoImplicit false
noncomputable section
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.ProductConstruction

open ProductPieces
open TubeExterior TubeExterior.CornerBands RimBands PolygonalCrossingResolution
open BoundaryAssembly

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Disk" => closedBall (0 : P2) 1
local notation "Rim" => sphere (0 : V2) 1

variable {X : Type} {ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R W Q : Set X}
  {S T C D : Set P2} {f₀ f₁ : P2 → X} {j : Bool → V2 → X}



theorem exists_homeomorph_of_actual_marked_panel_rim_with_equivalence
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {r w : ℝ} (hw : 0 < w) (hwr : w / 2 < r)
    (P : ∀ b, OriginalDiskProduct e (R \ U.map '' openTube r) (j b))
    [CompactSpace (⋃ k, range (pieceBottom U P r k))]
    {HN : ((⋃ k, range (pieceBottom U P r k)) × I) ≃ₜ
      (⋃ k, range (pieceParameter U P r k))}
    (hvalue : ∀ k x t, (HN (⟨pieceBottom U P r k x,
      mem_iUnion.mpr ⟨k,mem_range_self x⟩⟩,t) : X) =
        pieceParameter U P r k (x,t))
    {b : V2 × ℝ → X}
    (hbi : InjOn b (Rim ×ˢ I))
    (hperiod : ∀ i (s : ℝ), s ∈ Icc (i.val : ℝ) (i.val + 1) →
      ∀ t ∈ I,
        b (HamiltonIndexOne.squareCircle
          ((s : ℝ) : AddCircle (4 * (2 : ℝ))),t) =
          panelFamily U (P false) (P true) r w i (s - i.val,t))
    {B : Set X} {H : (Disk ×ˢ I : Set (P2 × ℝ)) ≃ₜ B}
    {k a₀ : P2 × ℝ → X}
    (hkv : ∀ p : (Disk ×ˢ I : Set (P2 × ℝ)), k p = (H p : X))
    (hann : EqOn k a₀ ((sphere (0 : P2) 1) ×ˢ I))
    {φ : V2 ≃ₜ P2}
    (hφ : ∀ z : V2, z ∈ Rim ↔ φ z ∈ sphere (0 : P2) 1)
    (hφsurj : ∀ z : (sphere (0 : P2) 1 : Set P2),
      ∃ v : (Rim : Set V2), φ v = z)
    (hmatch : ∀ z ∈ Rim, ∀ t ∈ I,
      b (z,t) = a₀ (φ z,t))
    (hinter :
      (⋃ k, range (pieceParameter U P r k)) ∩ B =
        b '' (Rim ×ˢ I)) :
    ∃ HB : ((Disk : Set P2) × I) ≃ₜ B,
    (∀ z t, (HB (z,t) : X) = k (z.1,t.1)) ∧ ∃ Hfinal :
        ((range (fun x : (⋃ k, range (pieceBottom U P r k)) =>
          (HN (x,⟨0,by norm_num⟩) : X)) ∪
          range (fun y : (Disk : Set P2) =>
            (HB (y,⟨0,by norm_num⟩) : X)) : Set X) × I) ≃ₜ
          ↥((⋃ k, range (pieceParameter U P r k)) ∪ B),
      (∀ x t, (Hfinal (⟨(HN (x,⟨0,by norm_num⟩) : X),
        mem_union_left (range (fun y : (Disk : Set P2) =>
          (HB (y,⟨0,by norm_num⟩) : X))) (mem_range_self x)⟩,t) : X) = HN (x,t)) ∧
      ∀ (y : (Disk : Set P2)) (t : I), (Hfinal (⟨(HB (y,⟨0,by norm_num⟩) : X),
        mem_union_right (range (fun x : (⋃ k, range (pieceBottom U P r k)) =>
        (HN (x,⟨0,by norm_num⟩) : X))) (mem_range_self y)⟩,t) : X) =
        HB (y,t) := by
  obtain ⟨rmap,hNparam,hNside⟩ :=
    exists_tube_side_base_map U hw hwr P HN hvalue b hperiod
  obtain ⟨HB,a,q,ha,hBparam,hBside,ha0,hHB⟩ :=
    ProductGluing.exists_final_ball_marked_annular_collar_on_panel_rim
      (X := X) (B := B) (H := H) (k := k) (a₀ := a₀)
      (φ := φ) hkv hann hφ hφsurj
  let aa : (Rim : Set V2) × I → X := fun p => b (p.1.1,p.2.1)
  have haa : ∀ p, a p = aa p := by
    intro p
    exact (ha0 p.1 p.2).trans (hmatch p.1 p.1.property p.2 p.2.property).symm
  have hai : Function.Injective aa := by
    intro p p' hpp'
    have hpval : ((p.1 : V2),(p.2 : ℝ)) =
        ((p'.1 : V2),(p'.2 : ℝ)) := by
      apply hbi
      · exact ⟨p.1.property,p.2.property⟩
      · exact ⟨p'.1.property,p'.2.property⟩
      · exact hpp'
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hpval))
      (Subtype.ext (congrArg Prod.snd hpval))
  have hNparam' : ∀ z t, (HN (rmap z,t) : X) = aa (z,t) := by
    intro z t
    exact hNparam z t
  have hNside' : ∀ x t, (HN (x,t) : X) ∈ range aa ↔ ∃ z, rmap z = x := by
    simpa only [aa] using hNside
  have hBparam' : ∀ z t, (HB (q z,t) : X) = aa (z,t) := by
    intro z t
    exact (hBparam z t).trans (haa (z,t))
  have harange : range aa = range a := by
    ext x
    constructor
    · rintro ⟨p,rfl⟩
      exact ⟨p,haa p⟩
    · rintro ⟨p,rfl⟩
      exact ⟨p,(haa p).symm⟩
  have hBside' : ∀ y t, (HB (y,t) : X) ∈ range aa ↔ ∃ z, q z = y := by
    intro y t
    rw [harange]
    exact hBside y t
  have harange' : range aa = b '' (Rim ×ˢ I) := by
    ext x
    constructor
    · rintro ⟨p,rfl⟩
      exact ⟨(p.1.1,p.2.1),⟨p.1.property,p.2.property⟩,rfl⟩
    · rintro ⟨⟨z,t⟩,hp,rfl⟩
      exact ⟨(⟨z,hp.1⟩,⟨t,hp.2⟩),rfl⟩
  have hinter' :
      (⋃ k, range (pieceParameter U P r k)) ∩ B = range aa :=
    hinter.trans harange'.symm
  obtain ⟨H₀,h₀,h₁⟩ :=
    ProductGluing.exists_homeomorph_of_annularly_attached_products
      HN HB hai hinter' hNparam' hBparam' hNside' hBside'
  exact ⟨HB, hHB, H₀, h₀, h₁⟩

theorem exists_homeomorph_of_actual_marked_panel_rim
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {r w : ℝ} (hw : 0 < w) (hwr : w / 2 < r)
    (P : ∀ b, OriginalDiskProduct e (R \ U.map '' openTube r) (j b))
    [CompactSpace (⋃ k, range (pieceBottom U P r k))]
    {HN : ((⋃ k, range (pieceBottom U P r k)) × I) ≃ₜ
      (⋃ k, range (pieceParameter U P r k))}
    (hvalue : ∀ k x t, (HN (⟨pieceBottom U P r k x,
      mem_iUnion.mpr ⟨k,mem_range_self x⟩⟩,t) : X) =
        pieceParameter U P r k (x,t))
    {b : V2 × ℝ → X}
    (hbi : InjOn b (Rim ×ˢ I))
    (hperiod : ∀ i (s : ℝ), s ∈ Icc (i.val : ℝ) (i.val + 1) →
      ∀ t ∈ I,
        b (HamiltonIndexOne.squareCircle
          ((s : ℝ) : AddCircle (4 * (2 : ℝ))),t) =
          panelFamily U (P false) (P true) r w i (s - i.val,t))
    {B : Set X} {H : (Disk ×ˢ I : Set (P2 × ℝ)) ≃ₜ B}
    {k : P2 × ℝ → X}
    (hkv : ∀ p : (Disk ×ˢ I : Set (P2 × ℝ)), k p = (H p : X))
    (hann : EqOn k (AnnularParameter.pairCylinder b) ((sphere (0 : P2) 1) ×ˢ I))
    (hinter :
      (⋃ k, range (pieceParameter U P r k)) ∩ B =
        b '' (Rim ×ˢ I)) :
    ∃ HB : ((Disk : Set P2) × I) ≃ₜ B,
    (∀ z t, (HB (z,t) : X) = k (z.1,t.1)) ∧ ∃ Hfinal :
        ((range (fun x : (⋃ k, range (pieceBottom U P r k)) =>
          (HN (x,⟨0,by norm_num⟩) : X)) ∪
          range (fun y : (Disk : Set P2) =>
            (HB (y,⟨0,by norm_num⟩) : X)) : Set X) × I) ≃ₜ
          ↥((⋃ k, range (pieceParameter U P r k)) ∪ B),
      (∀ x t, (Hfinal (⟨(HN (x,⟨0,by norm_num⟩) : X),
        mem_union_left (range (fun y : (Disk : Set P2) =>
        (HB (y,⟨0,by norm_num⟩) : X))) (mem_range_self x)⟩,t) : X) = HN (x,t)) ∧
      ∀ (y : (Disk : Set P2)) (t : I), (Hfinal (⟨(HB (y,⟨0,by norm_num⟩) : X),
        mem_union_right (range (fun x : (⋃ k, range (pieceBottom U P r k)) =>
        (HN (x,⟨0,by norm_num⟩) : X))) (mem_range_self y)⟩,t) : X) =
        HB (y,t) := by
  exact exists_homeomorph_of_actual_marked_panel_rim_with_equivalence U hw hwr P
    hvalue hbi hperiod hkv hann
    (φ := AnnularParameter.pairCoordinates.toHomeomorph)
    AnnularParameter.pairCoordinates_rim
    AnnularParameter.pairCoordinates_rim_surjective
    (fun z _ t _ => (AnnularParameter.pairCylinder_match b z t).symm) hinter

end PoincareConjecture.M76.Dehn.Annuli.ProductConstruction
