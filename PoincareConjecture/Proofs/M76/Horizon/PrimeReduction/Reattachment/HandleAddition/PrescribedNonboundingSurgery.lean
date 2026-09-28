import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SphereSurgeryNonbounding
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.PrescribedProductOnOppositeDomain
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.PrescribedWholeProductCollar








set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "Sphere" => sphere (0 : V3) 1
local notation "J" => Icc (-(1/2 : ℝ)) (1/2)

theorem ChartwisePLSphere.exists_prescribed_nonbounding_surgery
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R S : Set X}
    (s : ChartwisePLSphere e S) (hR : IsCompact R) (he : PLDomain e R)
    (hSR : S ⊆ interior R)
    (hn : ¬ ∃ B, B ⊆ R ∧ Nonempty (ChartwisePLBall e B S))
    (rho : V2 × ℝ → X)
    (hPL : PolyhedralPLInCharts e rho (Disk ×ˢ Icc (-1 : ℝ) 1))
    (hinj : InjOn rho (Disk ×ˢ Icc (-1 : ℝ) 1))
    (hinto : MapsTo rho (Disk ×ˢ Icc (-1 : ℝ) 1) (interior R))
    (hproper : ∀ z ∈ Disk ×ˢ Icc (-1 : ℝ) 1, rho z ∈ S ↔ z.1 ∈ Rim) :
    ∃ (K : Set X)
      (P : OriginalDiskProduct e (R ∩ (interior K)ᶜ) (fun z => rho (z,0)))
      (a r : Bool → Set V3),
      P.map = rho ∧
      (∀ b, IsFinitePLBallPair P2 (a b) (r b) ∧ a b ⊆ Sphere ∧
        IsFinitePLBallPair P2 (Sphere \ (a b \ r b)) (r b) ∧
        s.map '' r b = P.capRimSet b ∧ (s.map '' a b) ∩ P.closedStrip = s.map '' r b) ∧
      Disjoint (s.map '' a true) (s.map '' a false) ∧
      ((s.map '' a true) ∪ (s.map '' a false)) ∪ P.map '' (Rim ×ˢ J) = S ∧
      ∃ _t : ∀ b, ChartwisePLSphere e ((s.map '' a b) ∪ P.capDisk b),
        Disjoint ((s.map '' a true) ∪ P.capDisk true)
          ((s.map '' a false) ∪ P.capDisk false) ∧
        (((s.map '' a true) ∪ P.capDisk true) ∪
          ((s.map '' a false) ∪ P.capDisk false)) \ P.closedStrip = S \ P.closedStrip ∧
        (∀ b, (s.map '' a b) ∪ P.capDisk b ⊆ interior R) ∧
        ∃ b, ¬ ∃ B, B ⊆ R ∧
          Nonempty (ChartwisePLBall e B ((s.map '' a b) ∪ P.capDisk b)) := by
  classical
  let T := Icc (-1 : ℝ) 1
  let : PreconnectedSpace T := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  let j : V2 × T → X := fun z => rho (z.1,z.2)
  have hj : Continuous (fun z : Disk × T => j (z.1,z.2)) :=
    hPL.continuousOn.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)) (fun z => ⟨z.1.property,z.2.property⟩)
  have hjS (z : V2) (hz : z ∈ Disk) (t : T) : j (z,t) ∈ S ↔ z ∈ Rim :=
    hproper _ ⟨hz,t.property⟩
  have himage (A : Set V2) : j '' (A ×ˢ (univ : Set T)) = rho '' (A ×ˢ T) := by
    ext x
    constructor
    · rintro ⟨⟨z,t⟩,⟨hz,_⟩,rfl⟩
      exact ⟨(z,t),⟨hz,t.property⟩,rfl⟩
    · rintro ⟨⟨z,t⟩,⟨hz,ht⟩,rfl⟩
      exact ⟨(z,⟨t,ht⟩),⟨hz,mem_univ _⟩,rfl⟩
  obtain ⟨_,_,_,K,B,_,_,_,_,_,_,hK,hKPL,hKO,_,hBS,hfront,hcontact,_⟩ :=
    s.exists_original_opposite_unit_product_collar hR he hSR isOpen_univ
      (subset_univ S) j hj hjS
  have hcontact' : K ∩ (rho '' (Disk ×ˢ T)) = rho '' (Rim ×ˢ T) := by
    simpa only [himage] using hcontact
  obtain ⟨P,hP,_,_,_,_,_,_,_,_,_⟩ := exists_prescribed_product_on_opposite_domain
    hR he hK hKPL (fun x hx => (hKO hx).2) hBS hfront rho hPL hinj hinto hproper hcontact'
  have hPS : ∀ z ∈ Disk ×ˢ Icc (-1 : ℝ) 1, P.map z ∈ S ↔ z.1 ∈ Rim := by
    simpa only [hP] using hproper
  obtain ⟨a,r,har,had,hcover,t,_,hdis,houtside⟩ :=
    P.exists_original_separated_end_spheres s he.compatible hPS
  have hcapU (b : Bool) : P.capDisk b ⊆ P.closedStrip := by
    apply subset_trans _ P.endDisks_subset_closedStrip
    rw [P.endDisks_eq_capDisks]
    cases b
    · exact subset_union_left
    · exact subset_union_right
  have hUR : P.closedStrip ⊆ interior R := by
    rintro _ ⟨z,hz,rfl⟩
    rw [hP]
    exact hinto ⟨hz.1,by constructor <;> linarith [hz.2.1,hz.2.2]⟩
  have hretS (b : Bool) : s.map '' a b ⊆ S := by
    rintro _ ⟨z,hz,rfl⟩
    rw [s.map_eq ⟨z,(har b).2.1 hz⟩]
    exact (s.parametrization ⟨z,(har b).2.1 hz⟩).property
  have hNR (b : Bool) : (s.map '' a b) ∪ P.capDisk b ⊆ interior R :=
    union_subset ((hretS b).trans hSR) ((hcapU b).trans hUR)
  have hretstrip (b : Bool) : (s.map '' a b) ∩ P.closedStrip = P.capRimSet b :=
    (har b).2.2.2.2.trans (har b).2.2.2.1
  have hsi : InjOn s.map Sphere := by
    intro x hx y hy hxy
    rw [s.map_eq ⟨x,hx⟩,s.map_eq ⟨y,hy⟩] at hxy
    exact congrArg Subtype.val (s.parametrization.injective (Subtype.ext hxy))
  have hretout (b : Bool) : ((s.map '' a b) \ P.capDisk b).Nonempty := by
    obtain ⟨z,hza,hzr⟩ := (har b).1.sdiff_nonempty
    refine ⟨s.map z,⟨z,hza,rfl⟩,?_⟩
    intro hc
    have hr : s.map z ∈ s.map '' r b :=
      (har b).2.2.2.2.subset ⟨⟨z,hza,rfl⟩,hcapU b hc⟩
    obtain ⟨w,hwr,hwz⟩ := hr
    exact hzr (hsi ((har b).2.1 ((har b).1.1 hwr)) ((har b).2.1 hza) hwz ▸ hwr)
  refine ⟨K,P,a,r,hP,har,had,hcover,t,hdis,houtside,hNR,?_⟩
  by_contra h
  push Not at h
  apply hn
  apply P.sphere_bounds_of_two_separated_cap_fillings he hR s hSR hUR
    (fun b => s.map '' a b) hretS hretstrip hretout _ t hdis.symm h
  simpa only [union_comm (s.map '' a true) (s.map '' a false)] using hcover

end PoincareConjecture.M76
