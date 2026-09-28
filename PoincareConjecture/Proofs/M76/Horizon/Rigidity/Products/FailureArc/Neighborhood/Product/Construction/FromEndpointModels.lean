import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Construction.WholeRegion
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.EndDisks.EndpointFiniteDisk
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.EndDisks.ComplementContacts



set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.ProductConstruction
open TubeExterior TubeExterior.CornerBands RimBands PolygonalCrossingResolution
open ProductPieces ProductEndDisks BoundaryAssembly

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-1 : ℝ) 1

open Classical in
theorem exists_marked_product_of_endpoint_models
    {X ι : Type} [TopologicalSpace X] [T2Space X]
    (E : Bool → Type) [∀ b, NormedAddCommGroup (E b)]
    [∀ b, NormedSpace ℝ (E b)] [∀ b, FiniteDimensional ℝ (E b)]
    {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
    {S T C D : Set P2} {f₀ f₁ : P2 → X}
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (hI : IsPLIrreducible e R) (hconn : IsPreconnected R)
    {r w : ℝ} (hw : 0 < w) (hr1 : r < 1)
    {j : Bool → V2 → X}
    (P : ∀ b, OriginalDiskProduct e (R \ U.map '' openTube r) (j b))
    (F : Bool → V2 × ℝ → X) (ρ : Bool → ℝ)
    (hρ : ∀ b, 0 < ρ b) (hρr : ∀ b, ρ b < r) (hwρ : ∀ b, w/ρ b ≤ 1)
    (hmark : ∀ b, ∀ z ∈ Rim, ∀ s ∈ J,
      (P b).map (z,s) = F b (z,(w/ρ b)*s))
    (harms : ∀ side b : Bool, ∀ t ∈ I, ∀ s ∈ J,
      F side (rimArmPoint b t,s) = prescribedArmBand U r (ρ side) 0 1 side b (s,t))
    (hlateral : ∀ side, ∀ z ∈ Rim, ∀ s ∈ J,
      F side (z,s) ∈ U.map '' lateral r ↔ ∃ b : Bool, ∃ t ∈ I, z = rimArmPoint b t)
    (hdis : Disjoint ((P false).map '' (Disk ×ˢ J)) ((P true).map '' (Disk ×ˢ J)))
    (hopen : ∀ b v, 0 < v → v ≤ 1 →
      IsOpen ((Subtype.val : ↥(R \ U.map '' openTube r) → X) ⁻¹'
        ((P b).map '' (Disk ×ˢ Ioo (-v) v))))
    (hdistinct : connectedComponentIn (frontier R) (U.map ((0,0),0)) ≠
      connectedComponentIn (frontier R) (U.map ((0,0),1)))
    (K : ∀ b, SimplicialComplex ℝ (E b)) (hK : ∀ b, (K b).faces.Finite)
    (hpure : ∀ b, ∀ s ∈ (K b).faces, ∃ t ∈ (K b).faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ b, ∀ s ∈ (K b).faces, s.card = 2 →
      {t : Finset (E b) | t ∈ (K b).faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ b, ∀ p ∈ (K b).vertices, IsConnected ((K b).link p).space)
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
  dsimp only
  obtain ⟨B₀,L₀,_,_,hb₀,ha₀,hi₀,himage₀,hrim₀⟩ :=
    exists_original_endpoint_finite_disk U hR hI.1 hI.1.compatible hw hr1 P F ρ
      hρ hρr hwρ hmark harms hlateral hdis hopen hdistinct ⟨0,by norm_num⟩
      (Or.inl rfl) (K false) (hK false) (hpure false) (hcofaces false) (hlinks false)
      (hcount false) (Hmodel false) (a false) (ha false) (hav false)
  obtain ⟨B₁,L₁,_,_,hb₁,ha₁,hi₁,himage₁,hrim₁⟩ :=
    exists_original_endpoint_finite_disk U hR hI.1 hI.1.compatible hw hr1 P F ρ
      hρ hρr hwρ hmark harms hlateral hdis hopen hdistinct ⟨1,by norm_num⟩
      (Or.inr rfl) (K true) (hK true) (hpure true) (hcofaces true) (hlinks true)
      (hcount true) (Hmodel true) (a true) (ha true) (hav true)
  obtain ⟨hc₀,hold₀,hcover₀⟩ := endpoint_complement_contacts U hR hI.1 hw hr1.le
    P F ρ hρ hρr hwρ hmark harms hlateral hdis hdistinct ⟨0,by norm_num⟩ (Or.inl rfl)
  obtain ⟨hc₁,hold₁,hcover₁⟩ := endpoint_complement_contacts U hR hI.1 hw hr1.le
    P F ρ hρ hρr hwρ hmark harms hlateral hdis hdistinct ⟨1,by norm_num⟩ (Or.inr rfl)
  rw [← himage₀] at hc₀ hold₀ hcover₀
  rw [← himage₁] at hc₁ hold₁ hcover₁
  have hcontact₀ := hc₀.trans hrim₀.symm
  have hcontact₁ := hc₁.trans hrim₁.symm
  have hBdis : Disjoint (a false '' B₀.space) (a true '' B₁.space) := by
    rw [himage₀,himage₁]
    apply disjoint_left.mpr
    intro x hx₀ hx₁
    exact hdistinct ((connectedComponentIn_eq hx₀.1).trans
      (connectedComponentIn_eq hx₁.1).symm)
  obtain ⟨H,hzero,htop,_,_,hfront,_,hgraph⟩ :=
    exists_whole_region_product_of_end_disks U hR hI hconn hw hr1 P F ρ hρ hρr
      hwρ hmark harms hlateral hdis hopen hb₀ hb₁ ha₀ ha₁ hi₀ hi₁ hrim₀.symm
      hrim₁.symm hcontact₀ hcontact₁ hBdis hold₀ hold₁
  change (⋃ i, range (pieceBottom U P r i)) ∪ a false '' B₀.space = _ at hcover₀
  rw [← hcover₀]
  exact ⟨H,hzero,htop.trans hcover₁,hfront,hgraph⟩

end PoincareConjecture.M76.Dehn.Annuli.ProductConstruction
