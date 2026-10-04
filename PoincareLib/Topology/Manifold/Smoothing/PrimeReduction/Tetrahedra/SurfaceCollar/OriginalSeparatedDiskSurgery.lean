import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Tetrahedra.SurfaceCollar.OriginalSeparatedProductSpheres
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Cutting.OriginalWholeDiskProduct

/-!
# Separated circle surgery from the entire original proper disk

The original proper chartwise disk constructs its opposite collar and whole
disk product. Its actual two end spheres are disjoint and preserve the old
sphere outside the prescribed open support. The original cap is not truncated.
-/

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareMT.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "Sphere" => sphere (0 : V3) 1

theorem ChartwisePLSphere.exists_original_separated_disk_surgery
    {X ι E : Type*} [MetricSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {R S V : Set X} {d q : Set E}
    (s : ChartwisePLSphere e S) (hR : IsCompact R) (he : PLDomain e R)
    (hSR : S ⊆ interior R) (hd : IsFinitePLBallPair P2 d q) (j : E → X)
    (hj : PolyhedralPLInCharts e j d) (hji : InjOn j d)
    (hjR : MapsTo j d (interior R)) (hproper : ∀ z ∈ d, j z ∈ S ↔ z ∈ q)
    (hV : IsOpen V) (hjV : j '' d ⊆ V) :
    ∃ (K : Set X) (k : V2 → X) (P : OriginalDiskProduct e (R ∩ (interior K)ᶜ) k)
      (a r : Bool → Set V3),
      IsCompact K ∧ PLDomain e K ∧ k '' Disk = j '' d ∧ k '' Rim = j '' q ∧
      MapsTo P.map (Disk ×ˢ Icc (-1 : ℝ) 1) (V ∩ interior R) ∧
      (∀ z ∈ Disk ×ˢ Icc (-1 : ℝ) 1, P.map z ∈ S ↔ z.1 ∈ Rim) ∧
      (∀ b, IsFinitePLBallPair P2 (a b) (r b) ∧ a b ⊆ Sphere ∧
        IsFinitePLBallPair P2 (Sphere \ (a b \ r b)) (r b) ∧
        s.map '' r b = P.capRimSet b ∧ (s.map '' a b) ∩ P.closedStrip = s.map '' r b) ∧
      ∃ t : ∀ b, ChartwisePLSphere e ((s.map '' a b) ∪ P.capDisk b),
        (∀ b, EqOn (t b).map s.map (a b) ∧
          (t b).map '' (Sphere \ (a b \ r b)) = P.capDisk b) ∧
        Disjoint ((s.map '' a true) ∪ P.capDisk true)
          ((s.map '' a false) ∪ P.capDisk false) ∧
        (((s.map '' a true) ∪ P.capDisk true) ∪
          ((s.map '' a false) ∪ P.capDisk false)) \ P.closedStrip = S \ P.closedStrip ∧
        (((s.map '' a true) ∪ P.capDisk true) ∪
          ((s.map '' a false) ∪ P.capDisk false)) \ V = S \ V := by
  obtain ⟨K,_,_,k,hK,hKPL,_,_,_,_,_,_,_,_,hkD,hkQ,_,_,P,hP,hPS,_,_,_,_⟩ :=
    s.exists_original_whole_disk_product hR he hSR isOpen_univ (subset_univ S)
      hd j hj hji hjR hproper hV hjV
  obtain ⟨a,r,har,_,_,t,ht,hdis,houtside⟩ :=
    P.exists_original_separated_end_spheres s he.compatible hPS
  have hstripV : P.closedStrip ⊆ V := by
    rintro _ ⟨z,hz,rfl⟩
    exact (hP ⟨hz.1,by constructor <;> linarith [hz.2.1,hz.2.2]⟩).1.1
  refine ⟨K,k,P,a,r,hK,hKPL,hkD,hkQ,fun z hz => (hP hz).1,hPS,har,
    t,ht,hdis,houtside,?_⟩
  ext x
  constructor
  · intro hx
    have hn : x ∉ P.closedStrip := fun h => hx.2 (hstripV h)
    exact ⟨(houtside.subset ⟨hx.1,hn⟩).1,hx.2⟩
  · intro hx
    have hn : x ∉ P.closedStrip := fun h => hx.2 (hstripV h)
    exact ⟨(houtside.symm.subset ⟨hx.1,hn⟩).1,hx.2⟩

end PoincareMT.M76
