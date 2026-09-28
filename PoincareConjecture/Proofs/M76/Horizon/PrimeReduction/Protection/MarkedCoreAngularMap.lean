import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.OriginalDiskProtectedBallProduct
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.MarkedBallCoverLift
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneRetraction

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (-1:ℝ) 1
local notation "B2" => closedBall (0:P2) 1
local notation "S2" => sphere (0:P2) 1
local notation "Cube" => ((I ×ˢ I) ×ˢ I : Set (P2 × ℝ))

private theorem mem_plane_unit_ball_iff (x : P2) :
    x ∈ B2 ↔ x.1 ∈ I ∧ x.2 ∈ I := by
  simp only [mem_closedBall_zero_iff,Prod.norm_def,max_le_iff,Real.norm_eq_abs,
    abs_le,mem_Icc]

private def cylinderCubeHomeomorph : (I × B2) ≃ₜ Cube where
  toFun z := ⟨((z.2:P2),(z.1:ℝ)),(mem_plane_unit_ball_iff _).mp z.2.property,z.1.property⟩
  invFun z := (⟨z.val.2,z.property.2⟩,⟨z.val.1,(mem_plane_unit_ball_iff _).mpr z.property.1⟩)
  left_inv z := by rfl
  right_inv z := by rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem HamiltonMarkedProtectedBall.exists_original_disk_cylinder_product
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1) :
    ∃ P : (I × B2) ≃ₜ D,
      (∀ i : Bool, ∀ z : I × B2,
        (P z : LatticeHandleAmbient ι κ L) ∈ hamiltonMarkedProjection ι κ L ''
          ({fun _ : ι => if i then (1:ℝ) else -1} ×ˢ closedBall (0:κ→ℝ) (3/2)) ↔
          (z.1:ℝ) = if i then 1 else -1) ∧
      ∀ z : I × B2, (P z : LatticeHandleAmbient ι κ L) ∈
        frontier D \ (hamiltonAttachingBlock ι κ L (3/2) \
          hamiltonMarkedProjection ι κ L ''
            (sphere (0:ι→ℝ) 1 ×ˢ sphere (0:κ→ℝ) (3/2))) ↔ ‖(z.2:P2)‖ = 1 := by
  obtain ⟨p,G,hp,hval,hpi,himage,hfront,hbound,hatt,hends,hlat⟩ :=
    b.exists_original_disk_protected_ball_product_with_lateral he hdim hi
  let P := cylinderCubeHomeomorph.trans G
  refine ⟨P,?_,?_⟩
  · intro i z
    change (G (cylinderCubeHomeomorph z) : LatticeHandleAmbient ι κ L) ∈ _ ↔ _
    rw [←hval]
    exact hends i _ (cylinderCubeHomeomorph z).property
  · intro z
    change (G (cylinderCubeHomeomorph z) : LatticeHandleAmbient ι κ L) ∈ _ ↔ _
    rw [←hval,hlat _ (cylinderCubeHomeomorph z).property]
    change |(z.2:P2).1| = 1 ∨ |(z.2:P2).2| = 1 ↔ ‖(z.2:P2)‖ = 1
    have hz := (mem_plane_unit_ball_iff _).mp z.2.property
    rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs]
    rw [max_eq_iff]
    constructor
    · rintro (h|h)
      · exact Or.inl ⟨h,by rw [h]; exact abs_le.mpr hz.2⟩
      · exact Or.inr ⟨h,by rw [h]; exact abs_le.mpr hz.1⟩
    · rintro (h|h)
      · exact Or.inl h.1
      · exact Or.inr h.1

theorem HamiltonMarkedProtectedBall.exists_original_lifted_cylinder_angular_map
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1) :
    ∃ (P : (I × B2) ≃ₜ D) (lift : C(D,(ι→ℝ) × (κ→ℝ)))
      (angular : S2 ≃ₜ sphere (0:κ→ℝ) 1),
      (∀ i : Bool, ∀ z : I × B2,
        (P z : LatticeHandleAmbient ι κ L) ∈ hamiltonMarkedProjection ι κ L ''
          ({fun _ : ι => if i then (1:ℝ) else -1} ×ˢ closedBall (0:κ→ℝ) (3/2)) ↔
          (z.1:ℝ) = if i then 1 else -1) ∧
      (∀ z : I × B2, (P z : LatticeHandleAmbient ι κ L) ∈
        frontier D \ (hamiltonAttachingBlock ι κ L (3/2) \
          hamiltonMarkedProjection ι κ L ''
            (sphere (0:ι→ℝ) 1 ×ˢ sphere (0:κ→ℝ) (3/2))) ↔ ‖(z.2:P2)‖ = 1) ∧
      Function.Injective lift ∧
      (∀ x : D, hamiltonMarkedProjection ι κ L (lift x) = x) ∧
      (∀ (x:D) z, z ∈ closedBall (0:ι→ℝ) 1 ×ˢ closedBall (0:κ→ℝ) 1 →
        hamiltonMarkedProjection ι κ L z = x → lift x = z) ∧
      ∀ u : S2,
        (angular u : κ→ℝ) = (2/3:ℝ) •
          (lift (P (⟨-1,by norm_num⟩,⟨u,sphere_subset_closedBall u.property⟩))).2 := by
  classical
  let : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨P,hends,hlat⟩ := b.exists_original_disk_cylinder_product he hdim hi
  obtain ⟨lift,hli,hsection,hcorefix,hpatchfix,_⟩ :=
    b.exists_marked_standard_ball_lift (by omega)
  have hmark : D ∩ frontier (latticeHandleDomain ι κ L) =
      hamiltonAttachingBlock ι κ L (3/2) := by
    rcases b.position with ⟨hz,_⟩ | ⟨_,_,_,_,_,hm⟩
    · omega
    · exact hm
  have hneg : (fun _:ι => (-1:ℝ)) ∈ sphere (0:ι→ℝ) 1 := by
    rw [mem_sphere_zero_iff_norm,pi_norm_const,Real.norm_eq_abs]
    norm_num
  let endpoint : S2 → I × B2 := fun u =>
    (⟨-1,by norm_num⟩,⟨u,sphere_subset_closedBall u.property⟩)
  have hendpoint (u:S2) :
      (lift (P (endpoint u))).1 = (fun _:ι => (-1:ℝ)) ∧
      ‖(lift (P (endpoint u))).2‖ = (3/2:ℝ) := by
    have hatt := (hends false (endpoint u)).mpr (by rfl)
    obtain ⟨z,hz,hzx⟩ := hatt
    have hz0 : z.1 = (fun _:ι => (-1:ℝ)) := mem_singleton_iff.mp hz.1
    have hz1 : z.1 ∈ sphere (0:ι→ℝ) 1 := hz0.symm ▸ hneg
    have hfix := hpatchfix (P (endpoint u)) z ⟨hz1,hz.2⟩ hzx
    have hxAtt : (P (endpoint u) : LatticeHandleAmbient ι κ L) ∈
        hamiltonAttachingBlock ι κ L (3/2) := ⟨z,⟨hz1,hz.2⟩,hzx⟩
    have hxLat := (hlat (endpoint u)).mpr (mem_sphere_zero_iff_norm.mp u.property)
    have hxRim : (P (endpoint u) : LatticeHandleAmbient ι κ L) ∈
        hamiltonMarkedProjection ι κ L ''
          (sphere (0:ι→ℝ) 1 ×ˢ sphere (0:κ→ℝ) (3/2)) := by
      by_contra hn
      exact hxLat.2 ⟨hxAtt,hn⟩
    obtain ⟨w,hw,hwx⟩ := hxRim
    have hwfix := hpatchfix (P (endpoint u)) w
      ⟨hw.1,sphere_subset_closedBall hw.2⟩ hwx
    exact ⟨(congrArg Prod.fst hfix).trans hz0,
      (congrArg (fun z => ‖z.2‖) hwfix).trans (mem_sphere_zero_iff_norm.mp hw.2)⟩
  let a : S2 → sphere (0:κ→ℝ) 1 := fun u =>
    ⟨(2/3:ℝ) • (lift (P (endpoint u))).2,mem_sphere_zero_iff_norm.mpr (by
      rw [norm_smul,Real.norm_eq_abs,(hendpoint u).2]
      norm_num)⟩
  have ha : Continuous a := by dsimp [a,endpoint]; fun_prop
  have hai : Function.Injective a := by
    intro u v huv
    have hsecond : (lift (P (endpoint u))).2 = (lift (P (endpoint v))).2 := by
      have h := congrArg (fun x : sphere (0:κ→ℝ) 1 => (3/2:ℝ) • (x:κ→ℝ)) huv
      simpa [a,smul_smul] using h
    have hfirst := (hendpoint u).1.trans (hendpoint v).1.symm
    have hprod := P.injective (hli (Prod.ext hfirst hsecond))
    exact Subtype.ext (congrArg (fun z : I × B2 => (z.2:P2)) hprod)
  have has : Function.Surjective a := by
    intro v
    let z : (ι→ℝ) × (κ→ℝ) := ((fun _ => -1),(3/2:ℝ) • (v:κ→ℝ))
    have hz1 : z.1 ∈ sphere (0:ι→ℝ) 1 := hneg
    have hz2 : z.2 ∈ sphere (0:κ→ℝ) (3/2) := mem_sphere_zero_iff_norm.mpr (by
      dsimp [z]
      rw [norm_smul,Real.norm_eq_abs,mem_sphere_zero_iff_norm.mp v.property]
      norm_num)
    have hxOld : hamiltonMarkedProjection ι κ L z ∈
        D ∩ frontier (latticeHandleDomain ι κ L) :=
      hmark.symm.subset ⟨z,⟨hz1,sphere_subset_closedBall hz2⟩,rfl⟩
    let x : D := ⟨hamiltonMarkedProjection ι κ L z,hxOld.1⟩
    have hxFront : (x : LatticeHandleAmbient ι κ L) ∈ frontier D :=
      ((b.ball.frontier_inter_eq_of_subset b.subset_domain).symm.subset hxOld).1
    have hxLat : (x : LatticeHandleAmbient ι κ L) ∈
        frontier D \ (hamiltonAttachingBlock ι κ L (3/2) \
          hamiltonMarkedProjection ι κ L ''
            (sphere (0:ι→ℝ) 1 ×ˢ sphere (0:κ→ℝ) (3/2))) :=
      ⟨hxFront,fun h => h.2 ⟨z,⟨hz1,hz2⟩,rfl⟩⟩
    have hxP : (P (P.symm x) : LatticeHandleAmbient ι κ L) = x :=
      congrArg Subtype.val (P.apply_symm_apply x)
    have hs : ((P.symm x).1:ℝ) = -1 := (hends false _).mp (by
      rw [hxP]
      exact ⟨z,⟨rfl,sphere_subset_closedBall hz2⟩,rfl⟩)
    have hr : ‖((P.symm x).2:P2)‖ = 1 := (hlat _).mp (hxP.symm ▸ hxLat)
    let u : S2 := ⟨(P.symm x).2,mem_sphere_zero_iff_norm.mpr hr⟩
    have hendu : endpoint u = P.symm x := Prod.ext (Subtype.ext hs.symm) rfl
    refine ⟨u,Subtype.ext ?_⟩
    change (2/3:ℝ) • (lift (P (endpoint u))).2 = (v:κ→ℝ)
    rw [hendu,P.apply_symm_apply,hpatchfix x z ⟨hz1,sphere_subset_closedBall hz2⟩ rfl]
    dsimp [z]
    simp [smul_smul]
  let : CompactSpace S2 := isCompact_iff_compactSpace.mp (isCompact_sphere (0:P2) 1)
  let angular : S2 ≃ₜ sphere (0:κ→ℝ) 1 :=
    Continuous.homeoOfEquivCompactToT2 (f:=Equiv.ofBijective a ⟨hai,has⟩) ha
  exact ⟨P,lift,angular,hends,hlat,hli,hsection,hcorefix,fun _ => rfl⟩

end PoincareConjecture.M76
