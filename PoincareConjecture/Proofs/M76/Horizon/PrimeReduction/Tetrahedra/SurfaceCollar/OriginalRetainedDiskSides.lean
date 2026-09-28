import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.OriginalSeparatedProductSpheres
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallConnected

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76.OriginalDiskProduct
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "Sphere" => sphere (0 : V3) 1
local notation "J" => Icc (-(1/2 : ℝ)) (1/2)

theorem original_retained_disk_side_decomposition
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R S : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (s : ChartwisePLSphere e S)
    (d : Fin 2 → Set V3) {r : Set V3}
    (hd : ∀ b, IsFinitePLBallPair P2 (d b) r)
    (hwhole : d 0 ∪ d 1 = Sphere) (hinter : d 0 ∩ d 1 = r)
    (hband : P.map '' (Rim ×ˢ J) ⊆ S)
    (hcenter : P.map '' (Rim ×ˢ {(0 : ℝ)}) = s.map '' r)
    (hopen : IsOpen ((Subtype.val : S → X) ⁻¹'
      (P.map '' (Rim ×ˢ Ioo (-(1/2 : ℝ)) (1/2)))))
    (k q : Bool → Set V3)
    (hk : ∀ b, IsFinitePLBallPair P2 (k b) (q b) ∧ k b ⊆ Sphere ∧
      s.map '' q b = P.capRimSet b ∧ (s.map '' k b) ∩ P.closedStrip = s.map '' q b)
    (hcover : ((s.map '' k true) ∪ (s.map '' k false)) ∪
      (P.map '' (Rim ×ˢ J)) = S) :
    ∃ side : Bool → Fin 2, side false ≠ side true ∧
      ∀ b, s.map '' k b ⊆ s.map '' d (side b) ∧
        s.map '' d (side b) = (s.map '' k b) ∪
          (P.map '' (Rim ×ˢ (if b then Icc (0 : ℝ) (1/2) else Icc (-(1/2 : ℝ)) 0))) := by
  classical
  obtain ⟨side,hneq,hhalf,hclosed⟩ := P.exists_original_lateral_half_partition s d hd
    hwhole hinter hband hcenter hopen
  let D : Fin 2 → Set X := fun i => s.map '' d i
  let ret : Bool → Set X := fun b => s.map '' k b
  have hdS (i : Fin 2) : d i ⊆ Sphere := by
    fin_cases i
    · exact subset_union_left.trans hwhole.subset
    · exact subset_union_right.trans hwhole.subset
  have hsi : InjOn s.map Sphere := by
    intro x hx y hy hxy
    rw [s.map_eq ⟨x,hx⟩,s.map_eq ⟨y,hy⟩] at hxy
    exact congrArg Subtype.val (s.parametrization.injective (Subtype.ext hxy))
  have hDclosed (i : Fin 2) : IsClosed (D i) :=
    ((hd i).isCompact.image_of_continuousOn (s.piecewiseAffine.continuousOn.mono (hdS i))).isClosed
  have hDinter : D 0 ∩ D 1 = s.map '' r := by
    rw [←image_inter_on (fun x hx y hy hxy => hsi (hdS 1 hx) (hdS 0 hy) hxy),hinter]
  have hcross (a b : Fin 2) (hne : a ≠ b) : D a ∩ D b = s.map '' r := by
    fin_cases a <;> fin_cases b <;> simp_all [inter_comm]
  have hretS (b : Bool) : ret b ⊆ S := by
    rintro _ ⟨x,hx,rfl⟩
    rw [s.map_eq ⟨x,(hk b).2.1 hx⟩]
    exact (s.parametrization ⟨x,(hk b).2.1 hx⟩).property
  have hretcover (b : Bool) : ret b ⊆ D 0 ∪ D 1 := by
    intro x hx
    obtain ⟨z,hz,hzx⟩ := hx
    rcases hwhole.symm.subset ((hk b).2.1 hz) with h0 | h1
    · exact Or.inl ⟨z,h0,hzx⟩
    · exact Or.inr ⟨z,h1,hzx⟩
  have hretavoid (b : Bool) : Disjoint (ret b) (s.map '' r) := by
    apply disjoint_left.mpr
    intro x hx hr
    obtain ⟨⟨z,u⟩,⟨hz,hu⟩,hzu⟩ := hcenter.symm.subset hr
    have hu0 : u = 0 := hu
    have hxstrip : x ∈ P.closedStrip := by
      refine ⟨(z,u),⟨sphere_subset_closedBall hz,?_⟩,hzu⟩
      rw [hu0]
      norm_num
    have hcap := (hk b).2.2.1.subset ((hk b).2.2.2.subset ⟨hx,hxstrip⟩)
    obtain ⟨w,hw,hwx⟩ := hcap
    have heq := P.injective (by exact ⟨sphere_subset_closedBall hz,by rw [hu0]; norm_num⟩)
      (by
        refine ⟨sphere_subset_closedBall hw.1,?_⟩
        rw [show w.2 = if b then (1/2 : ℝ) else -(1/2) from hw.2]
        cases b <;> norm_num) (hzu.trans hwx.symm)
    have hh := congrArg Prod.snd heq
    dsimp at hh
    rw [hu0,show w.2 = if b then (1/2 : ℝ) else -(1/2) from hw.2] at hh
    cases b <;> norm_num at hh
  have hretSub (b : Bool) : ret b ⊆ D (side b) := by
    have hconn : IsPreconnected (ret b) :=
      (hk b).1.isConnected.isPreconnected.image s.map
        (s.piecewiseAffine.continuousOn.mono (hk b).2.1)
    have hmiss : ret b ∩ (D 0 ∩ D 1) = ∅ := by
      rw [hDinter]
      exact disjoint_iff_inter_eq_empty.mp (hretavoid b)
    have hex : ∃ v : Fin 2, ret b ⊆ D v := by
      rcases isPreconnected_iff_subset_of_disjoint_closed.mp hconn (D 0) (D 1)
        (hDclosed 0) (hDclosed 1) (hretcover b) hmiss with h | h
      · exact ⟨0,h⟩
      · exact ⟨1,h⟩
    obtain ⟨v,hv⟩ := hex
    by_cases heq : v = side b
    · exact heq ▸ hv
    have hone : (1 : V2) ∈ Rim := by simp
    let z : V2 × ℝ := (1,if b then 1/2 else -(1/2))
    have hzcap : P.map z ∈ P.capRimSet b := ⟨z,⟨hone,rfl⟩,rfl⟩
    have hzret : P.map z ∈ ret b := image_mono (hk b).1.1
      ((hk b).2.2.1.symm.subset hzcap)
    have hzhalf : P.map z ∈ D (side b) \ (s.map '' r) := by
      apply hhalf b
      refine ⟨z,⟨hone,?_⟩,rfl⟩
      cases b <;> norm_num [z]
    exact False.elim (hzhalf.2 ((hcross v (side b) heq).subset ⟨hv hzret,hzhalf.1⟩))
  refine ⟨side,hneq,fun b => ⟨hretSub b,?_⟩⟩
  have hnegb : side b ≠ side (!b) := by
    cases b
    · exact hneq
    · exact hneq.symm
  have hcover' : (ret b ∪ ret (!b)) ∪ (P.map '' (Rim ×ˢ J)) = S := by
    cases b
    · simpa only [Bool.not_false,union_comm (ret false) (ret true)] using hcover
    · exact hcover
  apply Subset.antisymm
  · intro x hx
    have hxS : x ∈ S := by
      obtain ⟨z,hz,rfl⟩ := hx
      rw [s.map_eq ⟨z,hdS _ hz⟩]
      exact (s.parametrization ⟨z,hdS _ hz⟩).property
    rcases hcover'.symm.subset hxS with (hb | ho) | hbandx
    · exact Or.inl hb
    · exact False.elim (disjoint_left.mp (hretavoid (!b)) ho
        ((hcross (side b) (side (!b)) hnegb).subset ⟨hx,hretSub (!b) ho⟩))
    · exact Or.inr ((hclosed b).subset ⟨hbandx,hx⟩)
  · rintro x (hx | hx)
    · exact hretSub b hx
    · exact ((hclosed b).symm.subset hx).2

end PoincareConjecture.M76.OriginalDiskProduct
