import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.OriginalRawSphereCut

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

structure MarkedSphereCut {X ι : Type*} [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V3) (R : Set X) (κ : Type*) where
  spheres : κ → Set X
  spherePL : ∀ i,ChartwisePLSphere e (spheres i)
  sphereInterior : ∀ i,spheres i ⊆ interior R
  sphereDisjoint : Pairwise fun i j => Disjoint (spheres i) (spheres j)
  collar : κ → Set X
  product : ∀ i,(spheres i × unitInterval) ≃ₜ closure (collar i)
  collarOpen : ∀ i,IsOpen (collar i)
  collarInterior : ∀ i,closure (collar i) ⊆ interior R
  collarDisjoint : Pairwise fun i j => Disjoint (closure (collar i)) (closure (collar j))
  openCoordinates : ∀ i z,(product i z : X) ∈ collar i ↔
    (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1
  centerCoordinates : ∀ i z,(product i z : X) ∈ spheres i ↔ (z.2 : ℝ) = 1/2
  sphereClosure : ∀ i,spheres i ⊆ closure (collar i)
  ports : κ × Bool → Set X
  portMap : ∀ b,spheres b.1 ≃ₜ ports b
  portPL : ∀ b,ChartwisePLSphere e (ports b)
  portDisjoint : Pairwise fun b d => Disjoint (ports b) (ports d)
  portClosure : ∀ b,ports b ⊆ closure (collar b.1)
  collarContact : ∀ i,closure (collar i) ∩ (R \ ⋃ j,collar j) =
    ports (i,false) ∪ ports (i,true)
  endpoints : ∀ i x,(product i (x,0) : X) = portMap (i,false) x ∧
    (product i (x,1) : X) = portMap (i,true) x
  center : ∀ i x,(product i (x,⟨(1/2 : ℝ),by norm_num⟩) : X) = x
  compactCut : IsCompact (R \ ⋃ i,collar i)
  plCut : PLDomain e (R \ ⋃ i,collar i)
  frontierCut : frontier (R \ ⋃ i,collar i) = frontier R ∪ ⋃ b,ports b

def MarkedSphereCut.carrier {X ι κ : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (c : MarkedSphereCut e R κ) : Set X := R \ ⋃ i,c.collar i

theorem exists_marked_sphere_cut
    {X ι κ : Type*} [MetricSpace X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3} {R U : Set X}
    (S : κ → Set X) (sS : ∀ i,ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hR : IsCompact R) (he : PLDomain e R)
    (hSR : ∀ i,S i ⊆ interior R) (hU : IsOpen U) (hSU : ∀ i,S i ⊆ U) :
    ∃ c : MarkedSphereCut e R κ,c.spheres = S ∧ ∀ i,closure (c.collar i) ⊆ U := by
  obtain ⟨Q,B,H,sB,O,W,_,hQeq,hQ,hPL,hO,hCC,hcontact,hBB,hfront,hW,hcenter,
      hopen,hS,hSC,_⟩ := exists_original_cut_with_raw_components S sS hdis hR he hSR hU hSU
  have hBcl (b : κ × Bool) : B b ⊆ closure (O b.1) := by
    rcases b with ⟨i,b⟩
    intro x hx
    obtain ⟨z,hz⟩ := (H (i,b)).surjective ⟨x,hx⟩
    have hval : (H (i,b) z : X) = x := congrArg Subtype.val hz
    cases b
    · have hh := (W i (z,0)).property
      rwa [(hW i z).1,hval] at hh
    · have hh := (W i (z,1)).property
      rwa [(hW i z).2,hval] at hh
  refine ⟨{
    spheres := S
    spherePL := sS
    sphereInterior := hSR
    sphereDisjoint := hdis
    collar := O
    product := W
    collarOpen := fun i => (hO i).1
    collarInterior := fun i => (hO i).2.2.2.trans inter_subset_right
    collarDisjoint := hCC
    openCoordinates := hopen
    centerCoordinates := hS
    sphereClosure := hSC
    ports := B
    portMap := H
    portPL := sB
    portDisjoint := hBB
    portClosure := hBcl
    collarContact := hQeq ▸ hcontact
    endpoints := hW
    center := hcenter
    compactCut := hQeq ▸ hQ
    plCut := hQeq ▸ hPL
    frontierCut := hQeq ▸ hfront },rfl,?_⟩
  exact fun i => (hO i).2.2.2.trans inter_subset_left

end PoincareConjecture.M76
