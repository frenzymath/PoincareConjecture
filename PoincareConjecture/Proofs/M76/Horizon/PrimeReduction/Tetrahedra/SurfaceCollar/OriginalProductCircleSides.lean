import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalDiskLateralOwner
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalRetainedDiskCap
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallTopology









set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76.OriginalDiskProduct
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "Sphere" => sphere (0 : V3) 1
local notation "J" => Icc (-(1/2 : ℝ)) (1/2)

theorem exists_original_lateral_half_sides
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R S : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (s : ChartwisePLSphere e S)
    (d : Fin 2 → Set V3) {r : Set V3}
    (hd : ∀ b, IsFinitePLBallPair (ℝ × ℝ) (d b) r)
    (hwhole : d 0 ∪ d 1 = Sphere) (hinter : d 0 ∩ d 1 = r)
    (hband : P.map '' (Rim ×ˢ J) ⊆ S)
    (hcenter : P.map '' (Rim ×ˢ {(0 : ℝ)}) = s.map '' r)
    (hopen : IsOpen ((Subtype.val : S → X) ⁻¹'
      (P.map '' (Rim ×ˢ Ioo (-(1/2 : ℝ)) (1/2))))) :
    ∃ side : Bool → Fin 2, side false ≠ side true ∧
      ∀ b, P.map '' (Rim ×ˢ (if b then Ioc (0 : ℝ) (1/2) else Ico (-(1/2 : ℝ)) 0))
        ⊆ (s.map '' d (side b)) \ (s.map '' r) := by
  classical
  let D : Fin 2 → Set X := fun b => s.map '' d b
  let H : Bool → Set ℝ := fun b => if b then Ioc 0 (1/2) else Ico (-(1/2)) 0
  have hdS (b : Fin 2) : d b ⊆ Sphere := by
    fin_cases b
    · exact subset_union_left.trans hwhole.subset
    · exact subset_union_right.trans hwhole.subset
  have hrS : r ⊆ Sphere := (hd 0).1.trans (hdS 0)
  have hsi : InjOn s.map Sphere := by
    intro x hx y hy hxy
    rw [s.map_eq ⟨x,hx⟩,s.map_eq ⟨y,hy⟩] at hxy
    exact congrArg Subtype.val (s.parametrization.injective (Subtype.ext hxy))
  have hDclosed (b : Fin 2) : IsClosed (D b) :=
    ((hd b).isCompact.image_of_continuousOn (s.piecewiseAffine.continuousOn.mono (hdS b))).isClosed
  have hDS : D 0 ∪ D 1 = S := by
    rw [←image_union,hwhole]
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      rw [s.map_eq ⟨z,hz⟩]
      exact (s.parametrization ⟨z,hz⟩).property
    · intro hx
      exact ⟨s.parametrization.symm ⟨x,hx⟩,(s.parametrization.symm ⟨x,hx⟩).property,
        (s.map_eq _).trans (congrArg Subtype.val (s.parametrization.apply_symm_apply _))⟩
  have hDinter : D 0 ∩ D 1 = s.map '' r := by
    rw [←image_inter_on (fun x hx y hy hxy => hsi (hdS 1 hx) (hdS 0 hy) hxy),hinter]
  have hHfull (b : Bool) : Rim ×ˢ H b ⊆ Disk ×ˢ Icc (-1 : ℝ) 1 := by
    rintro ⟨x,t⟩ ⟨hx,ht⟩
    refine ⟨sphere_subset_closedBall hx,?_⟩
    cases b <;> dsimp [H] at ht <;> constructor <;> linarith [ht.1,ht.2]
  have hHJ (b : Bool) : H b ⊆ J := by
    intro t ht
    cases b <;> dsimp [H] at ht <;> constructor <;> linarith [ht.1,ht.2]
  have havoid (b : Bool) : Disjoint (P.map '' (Rim ×ˢ H b)) (s.map '' r) := by
    apply disjoint_left.mpr
    rintro _ ⟨⟨x,t⟩,⟨hx,ht⟩,rfl⟩ hm
    obtain ⟨⟨y,u⟩,⟨hy,hu⟩,heq⟩ := hcenter.symm.subset hm
    have hu0 : u = 0 := hu
    have he := P.injective ⟨sphere_subset_closedBall hy,by rw [hu0]; norm_num⟩
      (hHfull b ⟨hx,ht⟩) heq
    have ht0 : t = 0 := (congrArg Prod.snd he).symm.trans hu0
    cases b <;> dsimp [H] at ht <;> rw [ht0] at ht <;> linarith [ht.1,ht.2]
  have hex (b : Bool) : ∃ v : Fin 2, P.map '' (Rim ×ˢ H b) ⊆ D v := by
    have hHconn : IsPreconnected (H b) := by
      cases b
      · exact isPreconnected_Ico
      · exact isPreconnected_Ioc
    have hconn := ((isConnected_sphere (by simp) (0 : V2) zero_le_one).isPreconnected.prod
      hHconn).image P.map (P.polyhedral.continuousOn.mono (hHfull b))
    have hcover : P.map '' (Rim ×ˢ H b) ⊆ D 0 ∪ D 1 := by
      rw [hDS]
      exact (image_mono (prod_mono Subset.rfl (hHJ b))).trans hband
    have hmiss : (P.map '' (Rim ×ˢ H b)) ∩ (D 0 ∩ D 1) = ∅ := by
      rw [hDinter]
      exact disjoint_iff_inter_eq_empty.mp (havoid b)
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hconn
      (D 0) (D 1) (hDclosed 0) (hDclosed 1) hcover hmiss with h | h
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
  choose side hside using hex
  refine ⟨side,?_,fun b x hx => ⟨hside b hx,disjoint_left.mp (havoid b) hx⟩⟩
  intro heq
  have hboth : P.map '' (Rim ×ˢ Ioo (-(1/2 : ℝ)) (1/2)) ⊆ D (side false) := by
    rintro _ ⟨⟨x,t⟩,⟨hx,ht⟩,rfl⟩
    rcases lt_trichotomy t 0 with hneg | hzero | hpos
    · exact hside false ⟨(x,t),⟨hx,ht.1.le,hneg⟩,rfl⟩
    · have hr := hcenter.subset ⟨(x,t),⟨hx,hzero⟩,rfl⟩
      exact image_mono (hd (side false)).1 hr
    · rw [heq]
      exact hside true ⟨(x,t),⟨hx,hpos,ht.2.le⟩,rfl⟩
  obtain ⟨x,hx⟩ := (isConnected_sphere (by simp) (0 : V2) zero_le_one).nonempty
  obtain ⟨z,hzr,hzmap⟩ := hcenter.subset ⟨(x,0),⟨hx,rfl⟩,rfl⟩
  let V : Set Sphere := s.parametrization ⁻¹' ((Subtype.val : S → X) ⁻¹'
    (P.map '' (Rim ×ˢ Ioo (-(1/2 : ℝ)) (1/2))))
  have hV : IsOpen V := hopen.preimage s.parametrization.continuous
  obtain ⟨W,hW,hWeq⟩ := isOpen_induced_iff.mp hV
  have hzW : z ∈ W := by
    apply (Set.ext_iff.mp hWeq ⟨z,hrS hzr⟩).mpr
    change (s.parametrization ⟨z,hrS hzr⟩ : X) ∈
      P.map '' (Rim ×ˢ Ioo (-(1/2 : ℝ)) (1/2))
    rw [←s.map_eq,hzmap]
    exact ⟨(x,0),⟨hx,by norm_num⟩,rfl⟩
  have hzother : z ∈ closure (d (side false).rev \ r) := by
    rw [(hd _).closure_sdiff]
    exact (hd _).1 hzr
  obtain ⟨y,hyW,hy⟩ := mem_closure_iff.mp hzother W hW hzW
  have hyband : s.map y ∈ P.map '' (Rim ×ˢ Ioo (-(1/2 : ℝ)) (1/2)) := by
    have hh := (Set.ext_iff.mp hWeq ⟨y,hdS _ hy.1⟩).mp hyW
    change (s.parametrization ⟨y,hdS _ hy.1⟩ : X) ∈
      P.map '' (Rim ×ˢ Ioo (-(1/2 : ℝ)) (1/2)) at hh
    rwa [←s.map_eq] at hh
  obtain ⟨w,hw,hwmap⟩ := hboth hyband
  have hwy := hsi (hdS _ hw) (hdS _ hy.1) hwmap
  have hysame : y ∈ d (side false) := hwy ▸ hw
  have hint : d (side false) ∩ d (side false).rev = r := by
    generalize side false = b
    fin_cases b
    · simpa using hinter
    · simpa [inter_comm] using hinter
  exact hy.2 (hint.subset ⟨hysame,hy.1⟩)

theorem exists_original_lateral_half_partition
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R S : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (s : ChartwisePLSphere e S)
    (d : Fin 2 → Set V3) {r : Set V3}
    (hd : ∀ b, IsFinitePLBallPair (ℝ × ℝ) (d b) r)
    (hwhole : d 0 ∪ d 1 = Sphere) (hinter : d 0 ∩ d 1 = r)
    (hband : P.map '' (Rim ×ˢ J) ⊆ S)
    (hcenter : P.map '' (Rim ×ˢ {(0 : ℝ)}) = s.map '' r)
    (hopen : IsOpen ((Subtype.val : S → X) ⁻¹'
      (P.map '' (Rim ×ˢ Ioo (-(1/2 : ℝ)) (1/2))))) :
    ∃ side : Bool → Fin 2, side false ≠ side true ∧
      (∀ b, P.map '' (Rim ×ˢ (if b then Ioc (0 : ℝ) (1/2) else Ico (-(1/2 : ℝ)) 0))
        ⊆ (s.map '' d (side b)) \ (s.map '' r)) ∧
      ∀ b, (P.map '' (Rim ×ˢ J)) ∩ (s.map '' d (side b)) =
        P.map '' (Rim ×ˢ (if b then Icc (0 : ℝ) (1/2) else Icc (-(1/2 : ℝ)) 0)) := by
  obtain ⟨side,hneq,hside⟩ := P.exists_original_lateral_half_sides s d hd
    hwhole hinter hband hcenter hopen
  have hdS (b : Fin 2) : d b ⊆ Sphere := by
    fin_cases b
    · exact subset_union_left.trans hwhole.subset
    · exact subset_union_right.trans hwhole.subset
  have hsi : InjOn s.map Sphere := by
    intro x hx y hy hxy
    rw [s.map_eq ⟨x,hx⟩,s.map_eq ⟨y,hy⟩] at hxy
    exact congrArg Subtype.val (s.parametrization.injective (Subtype.ext hxy))
  have hint : d (side false) ∩ d (side true) = r := by
    generalize side false = a at hneq ⊢
    generalize side true = b at hneq ⊢
    fin_cases a <;> fin_cases b <;> simp_all [inter_comm]
  have hphysical : (s.map '' d (side false)) ∩ (s.map '' d (side true)) = s.map '' r := by
    rw [←image_inter_on (fun x hx y hy hxy => hsi (hdS _ hx) (hdS _ hy) hxy),hint]
  refine ⟨side,hneq,hside,?_⟩
  intro b
  apply Subset.antisymm
  · rintro y ⟨⟨⟨x,t⟩,⟨hx,ht⟩,rfl⟩,hy⟩
    refine ⟨(x,t),⟨hx,?_⟩,rfl⟩
    cases b
    · refine ⟨ht.1,le_of_not_gt (fun hpos => ?_)⟩
      have hh := hside true ⟨(x,t),⟨hx,hpos,ht.2⟩,rfl⟩
      exact hh.2 (hphysical.subset ⟨hy,hh.1⟩)
    · refine ⟨le_of_not_gt (fun hneg => ?_),ht.2⟩
      have hh := hside false ⟨(x,t),⟨hx,ht.1,hneg⟩,rfl⟩
      exact hh.2 (hphysical.subset ⟨hh.1,hy⟩)
  · rintro y ⟨⟨x,t⟩,⟨hx,ht⟩,rfl⟩
    refine ⟨⟨(x,t),⟨hx,?_⟩,rfl⟩,?_⟩
    · cases b <;> simp only [Bool.false_eq_true,if_false,if_true] at ht <;>
        constructor <;> linarith [ht.1,ht.2]
    · by_cases ht0 : t = 0
      · exact image_mono (hd (side b)).1 (hcenter.subset ⟨(x,t),⟨hx,ht0⟩,rfl⟩)
      · apply (hside b _).1
        refine ⟨(x,t),⟨hx,?_⟩,rfl⟩
        cases b
        · exact ⟨ht.1,lt_of_le_of_ne ht.2 ht0⟩
        · exact ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),ht.2⟩

end PoincareConjecture.M76.OriginalDiskProduct
