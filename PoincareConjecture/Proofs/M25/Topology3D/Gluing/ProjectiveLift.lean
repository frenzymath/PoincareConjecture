import PoincareConjecture.Proofs.M25.Topology3D.Gluing.ProjectiveCover
import Mathlib.Topology.Homotopy.Lifting
import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Sphere

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

private theorem lift_sphere_continuous
    (L : C(UnitTwoSphere, projectiveCoverDomain p)) :
    Continuous (fun q : UnitTwoSphere => (L q).1) :=
  continuous_subtype_val.comp L.continuous

theorem exists_based_projective_sphere_lift
    (sigma : UnitTwoSphere → Q)
    (hs : ContMDiff (𝓡 2) (𝓡 3) ∞ sigma)
    (hinj : Function.Injective sigma)
    (hU : range sigma ⊆ U)
    (q0 : UnitTwoSphere) (x0 : UnitThreeSphere)
    (hx0 : x0 ∈ projectiveCoverDomain p)
    (hbase : C.cover x0 = sigma q0) :
    ∃ L : UnitTwoSphere → UnitThreeSphere,
      L q0 = x0 ∧
      (∀ q, L q ∈ projectiveCoverDomain p) ∧
      (∀ q, C.cover (L q) = sigma q) ∧
      ContMDiff (𝓡 2) (𝓡 3) ∞ L ∧
      IsClosedEmbedding L ∧
      ContMDiff (𝓡 2) (𝓡 3) ∞ (fun q => -L q) ∧
      IsClosedEmbedding (fun q => -L q) ∧
      Disjoint (range L) (range (fun q => -L q)) ∧
      projectiveCoverDomain p ∩ C.cover ⁻¹' range sigma =
        range L ∪ range (fun q => -L q) := by
  let : SimplyConnectedSpace UnitTwoSphere :=
    Poincare.Topology.sphereSimplyConnected_of_two_le (n := 2) (by norm_num)
  let : LocallyPathConnectedSpace UnitTwoSphere :=
    ChartedSpace.locallyPathConnectedSpace
      (EuclideanSpace ℝ (Fin 2)) UnitTwoSphere
  let sigmaU : C(UnitTwoSphere, U) :=
    { toFun := fun q => ⟨sigma q, hU (mem_range_self q)⟩
      continuous_toFun := (hs.continuous.comp continuous_id).subtype_mk _ }
  obtain ⟨Lsub, ⟨hL0, hL⟩, _⟩ :=
    (restrictedCover_isCoveringMap C).existsUnique_continuousMap_lifts
      sigmaU q0 ⟨x0, hx0⟩ (by
        apply Subtype.ext
        exact hbase)
  let L : UnitTwoSphere → UnitThreeSphere := fun q => (Lsub q).1
  have hLdomain (q : UnitTwoSphere) : L q ∈ projectiveCoverDomain p :=
    (Lsub q).2
  have hLbase : L q0 = x0 := congrArg Subtype.val hL0
  have hLcover (q : UnitTwoSphere) :
      C.cover (L q) = sigma q := by
    have hq := congrFun hL q
    exact congrArg Subtype.val hq
  have hLcont : Continuous L := lift_sphere_continuous Lsub
  let Lminus : UnitTwoSphere → UnitThreeSphere := fun q => -L q
  have hminus_domain (q : UnitTwoSphere) : Lminus q ∈ projectiveCoverDomain p :=
    (neg_mem_projectiveCoverDomain_iff p (L q)).mpr (hLdomain q)
  have hminus_cover (q : UnitTwoSphere) : C.cover (Lminus q) = sigma q := by
    dsimp [Lminus]
    rw [cover_neg C (hLdomain q), hLcover]
  have hLinj : Function.Injective L := by
    intro q r hqr
    apply hinj
    rw [← hLcover q, ← hLcover r, hqr]
  have hminus_inj : Function.Injective Lminus := by
    intro q r hqr
    apply hinj
    rw [← hminus_cover q, ← hminus_cover r, hqr]
  have hdisjoint : Disjoint (range L) (range Lminus) := by
    rw [Set.disjoint_left]
    rintro _ ⟨q, rfl⟩ ⟨r, hqr⟩
    have hqr' : q = r := by
      apply hinj
      calc
        sigma q = C.cover (L q) := (hLcover q).symm
        _ = C.cover (Lminus r) := congrArg C.cover hqr.symm
        _ = sigma r := hminus_cover r
    subst r
    exact (ne_neg_of_mem_unit_sphere ℝ (L q)) hqr.symm
  have hpreimage :
      projectiveCoverDomain p ∩ C.cover ⁻¹' range sigma =
        range L ∪ range Lminus := by
    apply Subset.antisymm
    · intro x hx
      rcases hx with ⟨hx, ⟨q, hq⟩⟩
      have hcovereq : C.cover x = C.cover (L q) :=
        hq.symm.trans (hLcover q).symm
      rcases (C.fibers x (L q) hx (hLdomain q)).mp hcovereq with h | h
      · exact Or.inl ⟨q, h.symm⟩
      · exact Or.inr ⟨q, h.symm⟩
    · intro x hx
      rcases hx with (⟨q, rfl⟩ | ⟨q, rfl⟩)
      · exact ⟨hLdomain q, ⟨q, (hLcover q).symm⟩⟩
      · exact ⟨hminus_domain q, ⟨q, (hminus_cover q).symm⟩⟩
  have hLsmooth : ContMDiff (𝓡 2) (𝓡 3) ∞ L := by
    intro q
    let hCq := C.local_diffeomorph ⟨L q, hLdomain q⟩
    let inv := hCq.localInverse
    have htarget : L q ∈ inv.target := hCq.localInverse_mem_target
    have hsource : sigma q ∈ inv.source := by
      rw [← hLcover q]
      exact hCq.localInverse_mem_source
    have hneighL : L ⁻¹' inv.target ∈ 𝓝 q :=
      hLcont.continuousAt (inv.open_target.mem_nhds htarget)
    have hneighS : sigma ⁻¹' inv.source ∈ 𝓝 q :=
      hs.continuous.continuousAt (inv.open_source.mem_nhds hsource)
    have hev : (fun r => L r) =ᶠ[𝓝 q] (inv ∘ sigma) := by
      filter_upwards [hneighL, hneighS] with r hrL hrS
      change L r = inv (sigma r)
      have hcover_r : sigma r = C.cover (L r) := (hLcover r).symm
      rw [hcover_r]
      exact (hCq.localInverse_left_inv hrL).symm
    exact (hCq.localInverse_contMDiffAt.comp_of_eq hs.contMDiffAt
      (hLcover q).symm).congr_of_eventuallyEq hev
  have hminus_smooth : ContMDiff (𝓡 2) (𝓡 3) ∞ Lminus := by
    let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩
    have hneg : ContMDiff (𝓡 3) (𝓡 3) ∞
        (fun x : UnitThreeSphere => -x) := contMDiff_neg_sphere
    exact hneg.comp hLsmooth
  have hLclosed : IsClosedEmbedding L :=
    hLsmooth.continuous.isClosedEmbedding hLinj
  have hminus_closed : IsClosedEmbedding Lminus :=
    hminus_smooth.continuous.isClosedEmbedding hminus_inj
  exact ⟨L, hLbase, hLdomain, hLcover, hLsmooth, hLclosed,
    hminus_smooth, hminus_closed, hdisjoint, hpreimage⟩

theorem projective_sphere_lift_mfderiv_injective
    (sigma : UnitTwoSphere → Q)
    (hreg : ∀ q, Function.Injective
      (mfderiv (𝓡 2) (𝓡 3) sigma q))
    {L : UnitTwoSphere → UnitThreeSphere}
    (hLdomain : ∀ q, L q ∈ projectiveCoverDomain p)
    (hLcover : ∀ q, C.cover (L q) = sigma q)
    (hLsmooth : ContMDiff (𝓡 2) (𝓡 3) ∞ L) :
    ∀ q, Function.Injective (mfderiv (𝓡 2) (𝓡 3) L q) := by
  intro q v w hvw
  apply hreg q
  have hcomp_v := mfderiv_comp_apply q
    ((C.local_diffeomorph ⟨L q, hLdomain q⟩).contMDiffAt.mdifferentiableAt (by simp))
    (hLsmooth.mdifferentiableAt (by simp)) v
  have hcomp_w := mfderiv_comp_apply q
    ((C.local_diffeomorph ⟨L q, hLdomain q⟩).contMDiffAt.mdifferentiableAt (by simp))
    (hLsmooth.mdifferentiableAt (by simp)) w
  have hfun : C.cover ∘ L = sigma := funext hLcover
  rw [hfun] at hcomp_v hcomp_w
  rw [hvw] at hcomp_v
  simpa using hcomp_v.trans hcomp_w.symm

end StandardPuncturedProjectiveCover
end PoincareConjecture.M25.Topology3D
