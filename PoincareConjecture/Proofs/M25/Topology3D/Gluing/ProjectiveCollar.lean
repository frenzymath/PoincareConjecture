import PoincareConjecture.Proofs.M25.Topology3D.Gluing.ProjectiveLift
import PoincareConjecture.Proofs.M25.Mathlib.LocalDiffeomorphLift
import Mathlib.Analysis.Convex.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M25.Topology3D
namespace StandardPuncturedProjectiveCover

variable {Q : Type u} [TopologicalSpace Q]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q]
  {p : RealProjectiveThree} {U : Set Q}
  (C : PoincareConjecture.StandardPuncturedProjectiveCover Q p U)

theorem exists_projective_collar_lift_of_slice
    (kappa : UnitTwoSphere × ℝ → Q) {a b t0 : ℝ}
    (ht0 : t0 ∈ Ioo a b)
    (hk : ContinuousOn kappa (univ ×ˢ Ioo a b))
    (hU : MapsTo kappa (univ ×ˢ Ioo a b) U)
    (L0 : UnitTwoSphere → UnitThreeSphere) (hL0 : Continuous L0)
    (hL0D : ∀ q, L0 q ∈ projectiveCoverDomain p)
    (hL0cover : ∀ q, C.cover (L0 q) = kappa (q, t0)) :
    ∃ L : UnitTwoSphere × ℝ → UnitThreeSphere,
      (∀ q, L (q, t0) = L0 q) ∧
      MapsTo L (univ ×ˢ Ioo a b) (projectiveCoverDomain p) ∧
      EqOn (C.cover ∘ L) kappa (univ ×ˢ Ioo a b) ∧
      ContinuousOn L (univ ×ˢ Ioo a b) := by
  classical
  let B := (univ ×ˢ Ioo a b : Set (UnitTwoSphere × ℝ))
  let R : unitInterval × B → UnitTwoSphere × ℝ :=
    fun w => (w.2.1.1, AffineMap.lineMap t0 w.2.1.2 w.1.1)
  have hRmem (w : unitInterval × B) : R w ∈ B := by
    refine ⟨mem_univ _, ?_⟩
    exact (convex_Ioo a b).lineMap_mem ht0 w.2.2.2 w.1.2
  have hRcont : Continuous R := by
    dsimp [R]
    simp only [AffineMap.lineMap_apply_ring]
    fun_prop
  let H : C(unitInterval × B, U) :=
    { toFun := fun w => ⟨kappa (R w), hU (hRmem w)⟩
      continuous_toFun := (hk.comp_continuous hRcont hRmem).subtype_mk _ }
  let f : C(B, projectiveCoverDomain p) :=
    { toFun := fun z => ⟨L0 z.1.1, hL0D z.1.1⟩
      continuous_toFun :=
        (hL0.comp (continuous_fst.comp continuous_subtype_val)).subtype_mk _ }
  have hH0 (z : B) : H (0, z) = restrictedCover C (f z) := by
    apply Subtype.ext
    simpa [H, R, f, restrictedCover] using (hL0cover z.1.1).symm
  let cov := restrictedCover_isCoveringMap C
  let lifted := cov.liftHomotopy H f hH0
  let Lsub : C(B, projectiveCoverDomain p) :=
    { toFun := fun z => lifted (1, z)
      continuous_toFun := lifted.continuous.comp (continuous_const.prodMk continuous_id) }
  have hsubcover (z : B) : C.cover (Lsub z).1 = kappa z.1 := by
    have hz := congrArg Subtype.val (congrFun (cov.liftHomotopy_lifts H f hH0) (1, z))
    simpa [Lsub, lifted, H, R, restrictedCover] using hz
  have hsubslice (q : UnitTwoSphere) :
      (Lsub ⟨(q, t0), mem_univ q, ht0⟩).1 = L0 q := by
    let z : B := ⟨(q, t0), mem_univ q, ht0⟩
    have hpath : Continuous (fun t : unitInterval => lifted (t, z)) :=
      lifted.continuous.comp (continuous_id.prodMk continuous_const)
    have hprojected (t t' : unitInterval) :
        restrictedCover C (lifted (t, z)) = restrictedCover C (lifted (t', z)) := by
      have ht : restrictedCover C (lifted (t, z)) = H (t, z) :=
        congrFun (cov.liftHomotopy_lifts H f hH0) (t, z)
      have ht' : restrictedCover C (lifted (t', z)) = H (t', z) :=
        congrFun (cov.liftHomotopy_lifts H f hH0) (t', z)
      rw [ht, ht']
      apply Subtype.ext
      simp [H, R, z]
    have heq := cov.const_of_comp hpath hprojected 1 0
    have hzero := cov.liftHomotopy_zero H f hH0 z
    exact congrArg Subtype.val (heq.trans hzero)
  let L : UnitTwoSphere × ℝ → UnitThreeSphere :=
    fun z => if hz : z ∈ B then (Lsub ⟨z, hz⟩).1 else L0 z.1
  have hLval (z : B) : L z.1 = (Lsub z).1 := by simp [L, z.2]
  have hcont : ContinuousOn L B := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : B.domRestrict L = fun z : B => (Lsub z).1 := funext hLval
    rw [heq]
    exact continuous_subtype_val.comp Lsub.continuous
  refine ⟨L, ?_, ?_, ?_, hcont⟩
  · intro q
    rw [hLval ⟨(q, t0), mem_univ q, ht0⟩]
    exact hsubslice q
  · intro z hz
    rw [hLval ⟨z, hz⟩]
    exact (Lsub ⟨z, hz⟩).2
  · intro z hz
    change C.cover (L z) = kappa z
    rw [hLval ⟨z, hz⟩]
    exact hsubcover ⟨z, hz⟩

theorem projective_collar_lift_isLocalDiffeomorphOn
    {kappa : UnitTwoSphere × ℝ → Q} {L : UnitTwoSphere × ℝ → UnitThreeSphere}
    {a b : ℝ}
    (hloc : IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      kappa (univ ×ˢ Ioo a b))
    (hL : ContinuousOn L (univ ×ˢ Ioo a b))
    (hLD : MapsTo L (univ ×ˢ Ioo a b) (projectiveCoverDomain p))
    (hcover : EqOn (C.cover ∘ L) kappa (univ ×ˢ Ioo a b)) :
    IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      L (univ ×ˢ Ioo a b) := by
  intro z
  have hnhds : (univ ×ˢ Ioo a b : Set (UnitTwoSphere × ℝ)) ∈ 𝓝 z.1 :=
    (isOpen_univ.prod isOpen_Ioo).mem_nhds z.2
  have hcomp := (hloc z).congr_of_eventuallyEq (Filter.eventuallyEq_of_mem hnhds hcover)
  exact hcomp.of_comp_left (C.local_diffeomorph ⟨L z.1, hLD z.2⟩)
    ((hL z.1 z.2).continuousAt hnhds)

theorem projective_collar_lift_antipodal_pair
    {kappa : UnitTwoSphere × ℝ → Q} {L : UnitTwoSphere × ℝ → UnitThreeSphere}
    {a b : ℝ}
    (hloc : IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      kappa (univ ×ˢ Ioo a b))
    (hinj : InjOn kappa (univ ×ˢ Ioo a b))
    (hL : ContinuousOn L (univ ×ˢ Ioo a b))
    (hLD : MapsTo L (univ ×ˢ Ioo a b) (projectiveCoverDomain p))
    (hcover : EqOn (C.cover ∘ L) kappa (univ ×ˢ Ioo a b)) :
    IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      L (univ ×ˢ Ioo a b) ∧
    InjOn L (univ ×ˢ Ioo a b) ∧
    MapsTo (fun z => -L z) (univ ×ˢ Ioo a b) (projectiveCoverDomain p) ∧
    EqOn (fun z => C.cover (-L z)) kappa (univ ×ˢ Ioo a b) ∧
    IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (fun z => -L z) (univ ×ˢ Ioo a b) ∧
    InjOn (fun z => -L z) (univ ×ˢ Ioo a b) ∧
    Disjoint (L '' (univ ×ˢ Ioo a b)) ((fun z => -L z) '' (univ ×ˢ Ioo a b)) ∧
    projectiveCoverDomain p ∩ C.cover ⁻¹' (kappa '' (univ ×ˢ Ioo a b)) =
      L '' (univ ×ˢ Ioo a b) ∪ (fun z => -L z) '' (univ ×ˢ Ioo a b) := by
  have hminusD : MapsTo (fun z => -L z) (univ ×ˢ Ioo a b)
      (projectiveCoverDomain p) := by
    intro z hz
    exact (neg_mem_projectiveCoverDomain_iff p (L z)).mpr (hLD hz)
  have hminuscover : EqOn (fun z => C.cover (-L z)) kappa (univ ×ˢ Ioo a b) := by
    intro z hz
    exact (cover_neg C (hLD hz)).trans (hcover hz)
  have hLinj : InjOn L (univ ×ˢ Ioo a b) := by
    intro z hz w hw heq
    apply hinj hz hw
    exact (hcover hz).symm.trans ((congrArg C.cover heq).trans (hcover hw))
  have hminusinj : InjOn (fun z => -L z) (univ ×ˢ Ioo a b) := by
    intro z hz w hw heq
    apply hinj hz hw
    exact (hminuscover hz).symm.trans ((congrArg C.cover heq).trans (hminuscover hw))
  refine ⟨projective_collar_lift_isLocalDiffeomorphOn C hloc hL hLD hcover,
    hLinj, hminusD, hminuscover,
    projective_collar_lift_isLocalDiffeomorphOn C hloc
      (continuous_neg.comp_continuousOn hL) hminusD hminuscover, hminusinj, ?_, ?_⟩
  · rw [Set.disjoint_left]
    rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, heq⟩
    have hzw : z = w := hinj hz hw
      ((hcover hz).symm.trans ((congrArg C.cover heq.symm).trans (hminuscover hw)))
    subst w
    exact ne_neg_of_mem_unit_sphere ℝ (L z) heq.symm
  · apply Subset.antisymm
    · rintro x ⟨hx, z, hz, heq⟩
      have hcov : C.cover x = C.cover (L z) := heq.symm.trans (hcover hz).symm
      rcases (C.fibers x (L z) hx (hLD hz)).mp hcov with h | h
      · exact Or.inl ⟨z, hz, h.symm⟩
      · exact Or.inr ⟨z, hz, h.symm⟩
    · rintro x (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
      · exact ⟨hLD hz, z, hz, (hcover hz).symm⟩
      · exact ⟨hminusD hz, z, hz, (hminuscover hz).symm⟩

theorem exists_smooth_projective_collar_lift_of_slice
    (kappa : UnitTwoSphere × ℝ → Q) {a b t0 : ℝ}
    (ht0 : t0 ∈ Ioo a b)
    (hloc : IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      kappa (univ ×ˢ Ioo a b))
    (hinj : InjOn kappa (univ ×ˢ Ioo a b))
    (hU : MapsTo kappa (univ ×ˢ Ioo a b) U)
    (L0 : UnitTwoSphere → UnitThreeSphere) (hL0 : Continuous L0)
    (hL0D : ∀ q, L0 q ∈ projectiveCoverDomain p)
    (hL0cover : ∀ q, C.cover (L0 q) = kappa (q, t0)) :
    ∃ L : UnitTwoSphere × ℝ → UnitThreeSphere,
      (∀ q, L (q, t0) = L0 q) ∧
      MapsTo L (univ ×ˢ Ioo a b) (projectiveCoverDomain p) ∧
      EqOn (C.cover ∘ L) kappa (univ ×ˢ Ioo a b) ∧
      IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ L (univ ×ˢ Ioo a b) ∧
      InjOn L (univ ×ˢ Ioo a b) ∧
      MapsTo (fun z => -L z) (univ ×ˢ Ioo a b) (projectiveCoverDomain p) ∧
      EqOn (fun z => C.cover (-L z)) kappa (univ ×ˢ Ioo a b) ∧
      IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
        (fun z => -L z) (univ ×ˢ Ioo a b) ∧
      InjOn (fun z => -L z) (univ ×ˢ Ioo a b) ∧
      Disjoint (L '' (univ ×ˢ Ioo a b)) ((fun z => -L z) '' (univ ×ˢ Ioo a b)) ∧
      projectiveCoverDomain p ∩ C.cover ⁻¹' (kappa '' (univ ×ˢ Ioo a b)) =
        L '' (univ ×ˢ Ioo a b) ∪ (fun z => -L z) '' (univ ×ˢ Ioo a b) := by
  obtain ⟨L, hslice, hLD, hcover, hcont⟩ :=
    exists_projective_collar_lift_of_slice C kappa ht0 hloc.contMDiffOn.continuousOn
      hU L0 hL0 hL0D hL0cover
  exact ⟨L, hslice, hLD, hcover,
    projective_collar_lift_antipodal_pair C hloc hinj hcont hLD hcover⟩

theorem exists_based_projective_collar_lift
    (kappa : UnitTwoSphere × ℝ → Q) {a b t0 : ℝ}
    (ht0 : t0 ∈ Ioo a b)
    (hloc : IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      kappa (univ ×ˢ Ioo a b))
    (hinj : InjOn kappa (univ ×ˢ Ioo a b))
    (hU : MapsTo kappa (univ ×ˢ Ioo a b) U)
    (q0 : UnitTwoSphere) (x0 : UnitThreeSphere)
    (hx0 : x0 ∈ projectiveCoverDomain p)
    (hbase : C.cover x0 = kappa (q0, t0)) :
    ∃ L : UnitTwoSphere × ℝ → UnitThreeSphere,
      L (q0, t0) = x0 ∧
      MapsTo L (univ ×ˢ Ioo a b) (projectiveCoverDomain p) ∧
      EqOn (C.cover ∘ L) kappa (univ ×ˢ Ioo a b) ∧
      IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ L (univ ×ˢ Ioo a b) ∧
      InjOn L (univ ×ˢ Ioo a b) ∧
      MapsTo (fun z => -L z) (univ ×ˢ Ioo a b) (projectiveCoverDomain p) ∧
      EqOn (fun z => C.cover (-L z)) kappa (univ ×ˢ Ioo a b) ∧
      IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
        (fun z => -L z) (univ ×ˢ Ioo a b) ∧
      InjOn (fun z => -L z) (univ ×ˢ Ioo a b) ∧
      Disjoint (L '' (univ ×ˢ Ioo a b)) ((fun z => -L z) '' (univ ×ˢ Ioo a b)) ∧
      projectiveCoverDomain p ∩ C.cover ⁻¹' (kappa '' (univ ×ˢ Ioo a b)) =
        L '' (univ ×ˢ Ioo a b) ∪ (fun z => -L z) '' (univ ×ˢ Ioo a b) := by
  have hsmooth : ContMDiff (𝓡 2) (𝓡 3) ∞ (fun q => kappa (q, t0)) :=
    hloc.contMDiffOn.comp_contMDiff (contMDiff_id.prodMk contMDiff_const)
      (fun q => ⟨mem_univ q, ht0⟩)
  have hsphereinj : Function.Injective (fun q : UnitTwoSphere => kappa (q, t0)) := by
    intro q r hqr
    exact congrArg Prod.fst (hinj ⟨mem_univ q, ht0⟩ ⟨mem_univ r, ht0⟩ hqr)
  have hsphereU : range (fun q : UnitTwoSphere => kappa (q, t0)) ⊆ U := by
    rintro _ ⟨q, rfl⟩
    exact hU ⟨mem_univ q, ht0⟩
  obtain ⟨L0, hL0base, hL0D, hL0cover, hL0smooth, _⟩ :=
    exists_based_projective_sphere_lift C (fun q => kappa (q, t0))
      hsmooth hsphereinj hsphereU q0 x0 hx0 hbase
  obtain ⟨L, hslice, hrest⟩ := exists_smooth_projective_collar_lift_of_slice
    C kappa ht0 hloc hinj hU L0 hL0smooth.continuous hL0D hL0cover
  exact ⟨L, (hslice q0).trans hL0base, hrest⟩

theorem projective_collar_lift_eqOn_of_base
    {L L' : UnitTwoSphere × ℝ → UnitThreeSphere} {a b t0 : ℝ}
    (ht0 : t0 ∈ Ioo a b) (q0 : UnitTwoSphere)
    (hL : ContinuousOn L (univ ×ˢ Ioo a b))
    (hL' : ContinuousOn L' (univ ×ˢ Ioo a b))
    (hLD : MapsTo L (univ ×ˢ Ioo a b) (projectiveCoverDomain p))
    (hL'D : MapsTo L' (univ ×ˢ Ioo a b) (projectiveCoverDomain p))
    (hc : EqOn (C.cover ∘ L) (C.cover ∘ L') (univ ×ˢ Ioo a b))
    (hb : L (q0, t0) = L' (q0, t0)) :
    EqOn L L' (univ ×ˢ Ioo a b) := by
  let : SimplyConnectedSpace UnitTwoSphere :=
    Poincare.Topology.sphereSimplyConnected_of_two_le (n := 2) (by norm_num)
  let B := (univ ×ˢ Ioo a b : Set (UnitTwoSphere × ℝ))
  let : PreconnectedSpace B :=
    Subtype.preconnectedSpace (isPreconnected_univ.prod isPreconnected_Ioo)
  let f : B → projectiveCoverDomain p := fun z => ⟨L z.1, hLD z.2⟩
  let g : B → projectiveCoverDomain p := fun z => ⟨L' z.1, hL'D z.2⟩
  have hf : Continuous f :=
    (continuousOn_iff_continuous_domRestrict.mp hL).subtype_mk _
  have hg : Continuous g :=
    (continuousOn_iff_continuous_domRestrict.mp hL').subtype_mk _
  have hfg : restrictedCover C ∘ f = restrictedCover C ∘ g := by
    funext z
    exact Subtype.ext (hc z.2)
  have heq := (restrictedCover_isCoveringMap C).eq_of_comp_eq hf hg hfg
    (⟨(q0, t0), mem_univ q0, ht0⟩ : B) (Subtype.ext hb)
  intro z hz
  exact congrArg Subtype.val (congrFun heq ⟨z, hz⟩)

theorem projective_collar_lift_closedEmbedding_on_Icc
    {L : UnitTwoSphere × ℝ → UnitThreeSphere} {a b r s : ℝ}
    (hL : ContinuousOn L (univ ×ˢ Ioo a b))
    (hinjL : InjOn L (univ ×ˢ Ioo a b))
    (hbuffer : a < r ∧ r ≤ s ∧ s < b) :
    IsClosedEmbedding (fun z : UnitTwoSphere × Icc r s => L (z.1, z.2.1)) := by
  have hmem (z : UnitTwoSphere × Icc r s) :
      (z.1, z.2.1) ∈ (univ ×ˢ Ioo a b : Set (UnitTwoSphere × ℝ)) :=
    ⟨mem_univ _, lt_of_lt_of_le hbuffer.1 z.2.2.1,
      lt_of_le_of_lt z.2.2.2 hbuffer.2.2⟩
  have hcont : Continuous (fun z : UnitTwoSphere × Icc r s => L (z.1, z.2.1)) :=
    hL.comp_continuous (continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd)) hmem
  apply hcont.isClosedEmbedding
  intro z w hzw
  have heq := hinjL (hmem z) (hmem w) hzw
  exact Prod.ext (congrArg (fun v : UnitTwoSphere × ℝ => v.1) heq)
    (Subtype.ext (congrArg (fun v : UnitTwoSphere × ℝ => v.2) heq))

end StandardPuncturedProjectiveCover
end PoincareConjecture.M25.Topology3D
