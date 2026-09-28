import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.MarkedCoreLateralAvoidance
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.MarkedCoreAngularMap
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.OriginalProtectedExterior








set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (-1:ℝ) 1
local notation "B2" => closedBall (0:P2) 1
local notation "S2" => sphere (0:P2) 1

theorem HamiltonMarkedProtectedBall.exists_original_core_lateral_retraction
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1) :
    let O := hamiltonMarkedProjection ι κ L ''
      (closedBall (0:ι→ℝ) 1 ×ˢ Metric.ball (0:κ→ℝ) 1)
    let T := frontier D \ (hamiltonAttachingBlock ι κ L (3/2) \
      hamiltonMarkedProjection ι κ L ''
        (sphere (0:ι→ℝ) 1 ×ˢ sphere (0:κ→ℝ) (3/2)))
    ∃ r : C(↥(D \ O),T), ∀ x : ↥(D \ O),
      (x:LatticeHandleAmbient ι κ L) ∈ T → (r x:LatticeHandleAmbient ι κ L) = x := by
  classical
  dsimp only
  let X := LatticeHandleAmbient ι κ L
  let O := hamiltonMarkedProjection ι κ L ''
    (closedBall (0:ι→ℝ) 1 ×ˢ Metric.ball (0:κ→ℝ) 1)
  let T := frontier D \ (hamiltonAttachingBlock ι κ L (3/2) \
    hamiltonMarkedProjection ι κ L ''
      (sphere (0:ι→ℝ) 1 ×ˢ sphere (0:κ→ℝ) (3/2)))
  change ∃ r : C(↥(D \ O),T), ∀ x : ↥(D \ O), (x:X) ∈ T → (r x:X) = x
  obtain ⟨P,lift,angular,hends,hlat,hli,hsection,hcorefix,hangular⟩ :=
    b.exists_original_lifted_cylinder_angular_map he hdim hi
  have hKT := b.core_disjoint_lateral (by omega)
  let M := I × B2
  let K : Set M := {z | (P z:X) ∈ hamiltonHandleBlock ι κ L 1}
  let V : Set M := {z | (P z:X) ∈ O}
  have hcoreCompact : IsCompact (hamiltonHandleBlock ι κ L 1) := by
    apply ((isCompact_closedBall (0:ι→ℝ) 1).prod
      (isCompact_closedBall (0:κ→ℝ) 1)).image
    unfold hamiltonMarkedProjection
    fun_prop
  have hK : IsCompact K :=
    (hcoreCompact.isClosed.preimage (continuous_subtype_val.comp P.continuous)).isCompact
  have hVK : V ⊆ K := by
    rintro z ⟨w,hw,hwz⟩
    exact ⟨w,⟨hw.1,ball_subset_closedBall hw.2⟩,hwz⟩
  have hKr (z:M) (hz:z∈K) : ‖(z.2:P2)‖ < 1 := by
    apply lt_of_le_of_ne (mem_closedBall_zero_iff.mp z.2.property)
    intro heq
    exact disjoint_left.mp hKT hz ((hlat z).mpr heq)
  let free : C((Vᶜ:Set M),κ→ℝ) :=
    ⟨fun z => (lift (P z.val)).2,by fun_prop⟩
  have hfree (z:(Vᶜ:Set M)) : 0 < ‖free z‖ := by
    apply norm_pos_iff.mpr
    intro hz
    apply z.property
    change (P z.val:X) ∈ O
    refine ⟨lift (P z.val),⟨?_,?_⟩,hsection _⟩
    · have hR := b.subset_domain (P z.val).property
      have hfirst := congrArg Prod.fst (hsection (P z.val))
      change (lift (P z.val)).1 = (P z.val).val.1 at hfirst
      rw [hfirst]
      exact hR.1
    · change free z ∈ Metric.ball (0:κ→ℝ) 1
      rw [hz]
      exact mem_ball_self (by norm_num)
  let normalized : C((Vᶜ:Set M),sphere (0:κ→ℝ) 1) :=
    ⟨fun z => ⟨‖free z‖⁻¹ • free z,mem_sphere_zero_iff_norm.mpr (by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (hfree z)),
        inv_mul_cancel₀ (ne_of_gt (hfree z))])⟩,
      Continuous.subtype_mk ((free.continuous.norm.inv₀ (fun z => ne_of_gt (hfree z))).smul
        free.continuous) _⟩
  let rho : C((Vᶜ:Set M),S2) := ⟨fun z => angular.symm (normalized z),by fun_prop⟩
  have hminus (u:S2) (z:(Vᶜ:Set M))
      (hs : (z.val.1:ℝ) = -1) (hv : (z.val.2:P2) = (1:ℝ) • (u:P2)) :
      rho z = u := by
    have hz : z.val = (⟨-1,by norm_num⟩,⟨u,sphere_subset_closedBall u.property⟩) :=
      Prod.ext (Subtype.ext hs) (Subtype.ext (by simpa using hv))
    have ha : (angular u:κ→ℝ) = (2/3:ℝ) • free z := by
      dsimp [free]
      rw [hz]
      exact hangular u
    have hn : ‖free z‖ = (3/2:ℝ) := by
      have hh := mem_sphere_zero_iff_norm.mp (angular u).property
      rw [ha,norm_smul,Real.norm_eq_abs] at hh
      norm_num at hh
      linarith
    have hnu : normalized z = angular u := by
      apply Subtype.ext
      change ‖free z‖⁻¹ • free z = (angular u:κ→ℝ)
      rw [hn,ha]
      norm_num
    change angular.symm (normalized z) = u
    rw [hnu,angular.symm_apply_apply]
  obtain ⟨rp,hrp⟩ := HamiltonIndexOne.exists_marked_product_complement_retraction
    (by norm_num : (0:ℝ)<1) K V hK hVK hKr rho hminus
  let inc : C(I × S2,M) :=
    ⟨fun z => (z.1,⟨z.2,sphere_subset_closedBall z.2.property⟩),by fun_prop⟩
  let lateral : C(I × S2,T) :=
    ⟨fun z => ⟨P (inc z),(hlat (inc z)).mpr
      (mem_sphere_zero_iff_norm.mp z.2.property)⟩,by fun_prop⟩
  let toD : C(↥(D \ O),D) := ⟨fun z => ⟨z,z.property.1⟩,by fun_prop⟩
  let pull : C(↥(D \ O),(Vᶜ:Set M)) :=
    ⟨fun z => ⟨P.symm (toD z),by
      change ¬ (P (P.symm (toD z)):X) ∈ O
      rw [P.apply_symm_apply]
      exact z.property.2⟩,by fun_prop⟩
  refine ⟨lateral.comp (rp.comp pull),?_⟩
  intro x hx
  let m : M := P.symm (toD x)
  have hm : (P m:X) = x := congrArg Subtype.val (P.apply_symm_apply (toD x))
  have hn : ‖(m.2:P2)‖ = 1 := (hlat m).mp (hm.symm ▸ hx)
  let u : S2 := ⟨m.2,mem_sphere_zero_iff_norm.mpr hn⟩
  have hr : rp (pull x) = (m.1,u) := hrp m.1 u (pull x) rfl (by simp [u,pull,m])
  change (P (inc (rp (pull x))):X) = x
  rw [hr]
  exact hm

theorem HamiltonMarkedProtectedBall.exists_original_exterior_retraction_with_lateral
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1) :
    let R := latticeHandleDomain ι κ L
    let O := hamiltonMarkedProjection ι κ L ''
      (closedBall (0:ι→ℝ) 1 ×ˢ Metric.ball (0:κ→ℝ) 1)
    let E := closure (R \ D)
    E ⊆ R \ O ∧ ∃ r : C(↥(R \ O),E),
      (∀ x : ↥(R \ O), (x:LatticeHandleAmbient ι κ L) ∈ E →
        (r x:LatticeHandleAmbient ι κ L) = x) ∧
      ∀ x : ↥(R \ O), (x:LatticeHandleAmbient ι κ L) ∈ D →
        (r x:LatticeHandleAmbient ι κ L) ∈ frontier D \
          (hamiltonAttachingBlock ι κ L (3/2) \
            hamiltonMarkedProjection ι κ L ''
              (sphere (0:ι→ℝ) 1 ×ˢ sphere (0:κ→ℝ) (3/2))) := by
  classical
  dsimp only
  let X := LatticeHandleAmbient ι κ L
  let R := latticeHandleDomain ι κ L
  let O := hamiltonMarkedProjection ι κ L ''
    (closedBall (0:ι→ℝ) 1 ×ˢ Metric.ball (0:κ→ℝ) 1)
  let E := closure (R \ D)
  let T := frontier D \ (hamiltonAttachingBlock ι κ L (3/2) \
    hamiltonMarkedProjection ι κ L ''
      (sphere (0:ι→ℝ) 1 ×ˢ sphere (0:κ→ℝ) (3/2)))
  change E ⊆ R \ O ∧ ∃ r : C(↥(R \ O),E),
    (∀ x : ↥(R \ O), (x:X) ∈ E → (r x:X) = x) ∧
    ∀ x : ↥(R \ O), (x:X) ∈ D → (r x:X) ∈ T
  obtain ⟨hEc,hER,hcoverED,hcontact,_,_,_⟩ := b.closed_complement_geometry he hdim hi
  obtain ⟨rD,hrD⟩ := b.exists_original_core_lateral_retraction he hdim hi
  have hKT := b.core_disjoint_lateral (by omega)
  have hOK : O ⊆ hamiltonHandleBlock ι κ L 1 := by
    rintro x ⟨z,hz,hzx⟩
    exact ⟨z,⟨hz.1,ball_subset_closedBall hz.2⟩,hzx⟩
  have hKD : hamiltonHandleBlock ι κ L 1 ⊆ D := by
    rcases b.position with ⟨hzero,_⟩ | ⟨_,hcore,_⟩
    · omega
    · exact hcore
  have hEE0 : E ⊆ R \ O := by
    intro x hx
    refine ⟨hER hx,?_⟩
    intro hxO
    exact disjoint_left.mp hKT (hOK hxO) (hcontact.subset ⟨hx,hKD (hOK hxO)⟩)
  have hTE : T ⊆ E := fun _ hx => (hcontact.symm.subset hx).1
  let s : Set ↥(R \ O) := Subtype.val ⁻¹' E
  let t : Set ↥(R \ O) := Subtype.val ⁻¹' D
  let f : C(s,E) := ⟨fun x => ⟨x.val.val,x.property⟩,by fun_prop⟩
  let pull : C(t,↥(D \ O)) :=
    ⟨fun x => ⟨x.val.val,⟨x.property,x.val.property.2⟩⟩,by fun_prop⟩
  let inc : C(T,E) := ⟨fun x => ⟨x,hTE x.property⟩,by fun_prop⟩
  let g : C(t,E) := inc.comp (rD.comp pull)
  have hcover : s ∪ t = univ := by
    ext x
    apply iff_true_intro
    exact hcoverED.symm.subset x.property.1
  obtain ⟨r,hr,hright⟩ := HamiltonIndexOne.glue_closed_cover s t
    (isClosed_closure.preimage continuous_subtype_val)
    (b.ball.isCompact.isClosed.preimage continuous_subtype_val) hcover f g (by
      intro x hxs hxt
      apply Subtype.ext
      exact (hrD (pull ⟨x,hxt⟩) (hcontact.subset ⟨hxs,hxt⟩)).symm)
  refine ⟨hEE0,r,?_,?_⟩
  · intro x hx
    exact congrArg Subtype.val (hr ⟨x,hx⟩)
  · intro x hx
    rw [hright ⟨x,hx⟩]
    exact (rD (pull ⟨x,hx⟩)).property

theorem HamiltonMarkedProtectedBall.exists_original_exterior_retraction
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1) :
    let R := latticeHandleDomain ι κ L
    let O := hamiltonMarkedProjection ι κ L ''
      (closedBall (0:ι→ℝ) 1 ×ˢ Metric.ball (0:κ→ℝ) 1)
    let E := closure (R \ D)
    E ⊆ R \ O ∧ ∃ r : C(↥(R \ O),E),
      ∀ x : ↥(R \ O), (x:LatticeHandleAmbient ι κ L) ∈ E →
        (r x:LatticeHandleAmbient ι κ L) = x := by
  obtain ⟨h,r,hfix,_⟩ := b.exists_original_exterior_retraction_with_lateral he hdim hi
  exact ⟨h,r,hfix⟩

end PoincareConjecture.M76
