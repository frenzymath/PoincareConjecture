import PoincareLib.Geometry.RicciFlow.Blowup.Construction.Analysis.SmoothCoverLift
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.ShortTime.StaticLimit.StaticNullField
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.ShortTime.Nullity.NullNeckTransversality
import PoincareLib.Topology.Homotopy.Sphere.SphereConnectivity

/-!
# A lifted neck sphere transverse to the unit null field

The actual central sphere lifts through the unit Ricci-kernel cover.
Its coordinate left inverse and the projected field identity prove
injectivity of the lifted differential and transversality to the fixed
tautological field. This supplies the compact section for the flowout
argument in Morgan--Tian Claim 11.7, pp. 270-271.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Manifold PoincareMT.RicciFlow.Splitting
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M30

/-- The actual central sphere of a sufficiently small neck has a smooth
lift transverse to the literal unit Ricci-kernel field, with injective
differential (Claim 11.7, pp. 270-271). -/
theorem exists_neck_lifted_sphere_transverse_unitRicciKernelField :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (N : EpsilonNeck g) (D : LeviCivitaData g), N.epsilon ≤ epsilon0 →
      ∀ (hc : IsCoveringMap (unitRicciKernelProjection D)),
        (∀ x : M, Nat.card (unitRicciKernelProjection D ⁻¹' {x}) = 2) →
      letI := unitRicciKernelChartedSpace D hc
      letI := unitRicciKernelIsManifold D hc
      ∃ j : UnitTwoSphere → UnitRicciKernel D,
        ContMDiff (𝓡 2) (𝓡 3) ∞ j ∧
        unitRicciKernelProjection D ∘ j = (fun q => N.coordinate_map (q, 0)) ∧
        (∀ q, Function.Injective (mfderiv (𝓡 2) (𝓡 3) j q)) ∧
        ∀ q, ¬ ∃ v : TangentSpace (𝓡 2) q,
          mfderiv (𝓡 2) (𝓡 3) j q v = unitRicciKernelField D hc (j q) := by
  classical
  obtain ⟨epsilon0, hepsilon0, hsmall, htrans⟩ :=
    exists_neck_central_sphere_ricci_null_transversality.{u}
  refine ⟨epsilon0, hepsilon0, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g N D hN hc hcard
  let := unitRicciKernelChartedSpace D hc
  let := unitRicciKernelIsManifold D hc
  let : SimplyConnectedSpace UnitTwoSphere :=
    Poincare.Topology.sphere_simplyConnectedSpace_of_two_lt_finrank (by simp)
  let : LocallyPathConnectedSpace UnitTwoSphere :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) UnitTwoSphere
  let i : UnitTwoSphere → M := fun q => N.coordinate_map (q, 0)
  have hi : ContMDiff (𝓡 2) (𝓡 3) ∞ i := N.centralSphere_contMDiff
  have hpi := unitRicciKernelProjection_isLocalDiffeomorph D hc
  let q0 : UnitTwoSphere := (N.coordinate_inverse N.center).1
  have hfiber : Nonempty (unitRicciKernelProjection D ⁻¹' {i q0}) :=
    (Nat.card_ne_zero.mp (by rw [hcard]; decide)).1
  obtain ⟨p0⟩ := hfiber
  obtain ⟨j, hj, _, hproj⟩ := exists_contMDiff_covering_lift hc hpi hi q0 p0.1 p0.2
  have hz (q : UnitTwoSphere) : (q, (0 : ℝ)) ∈ N.cylinderDomain :=
    ⟨mem_univ _, neg_lt_zero.mpr (inv_pos.mpr N.epsilon_pos),
      inv_pos.mpr N.epsilon_pos⟩
  let k : M → UnitTwoSphere := fun x => (N.coordinate_inverse x).1
  have hkcomp : k ∘ i = id := by
    funext q
    exact congrArg Prod.fst (N.coordinate_inverse_coordinate_map (hz q))
  have hk (q : UnitTwoSphere) : MDifferentiableAt (𝓡 3) (𝓡 2) k (i q) :=
    (contMDiffAt_fst.comp (i q) (N.coordinate_inverse_smooth.contMDiffAt
      (N.carrier_open.mem_nhds (N.coordinate_map_mem (hz q))))).mdifferentiableAt (by simp)
  have hi_inj (q : UnitTwoSphere) : Function.Injective (mfderiv (𝓡 2) (𝓡 3) i q) := by
    have hcomp : (mfderiv (𝓡 3) (𝓡 2) k (i q)).comp (mfderiv (𝓡 2) (𝓡 3) i q) =
        ContinuousLinearMap.id ℝ (TangentSpace (𝓡 2) q) := by
      rw [← mfderiv_comp q (hk q) (hi.mdifferentiable (by simp) q), hkcomp]
      exact mfderiv_id
    have hleft (v : TangentSpace (𝓡 2) q) :
        mfderiv (𝓡 3) (𝓡 2) k (i q) (mfderiv (𝓡 2) (𝓡 3) i q v) = v :=
      congrArg (fun L => L v) hcomp
    intro v w hvw
    exact (hleft v).symm.trans
      ((congrArg (mfderiv (𝓡 3) (𝓡 2) k (i q)) hvw).trans (hleft w))
  have hderiv (q : UnitTwoSphere) :
      (mfderiv (𝓡 3) (𝓡 3) (unitRicciKernelProjection D) (j q)).comp
        (mfderiv (𝓡 2) (𝓡 3) j q) = mfderiv (𝓡 2) (𝓡 3) i q := by
    rw [← mfderiv_comp q (hpi.contMDiff.mdifferentiable (by simp) (j q))
      (hj.mdifferentiable (by simp) q), hproj]
  refine ⟨j, hj, hproj, ?_, ?_⟩
  · intro q v w hvw
    apply hi_inj q
    have heq := congrArg (mfderiv (𝓡 3) (𝓡 3) (unitRicciKernelProjection D) (j q)) hvw
    change ((mfderiv (𝓡 3) (𝓡 3) (unitRicciKernelProjection D) (j q)).comp
      (mfderiv (𝓡 2) (𝓡 3) j q)) v =
      ((mfderiv (𝓡 3) (𝓡 3) (unitRicciKernelProjection D) (j q)).comp
        (mfderiv (𝓡 2) (𝓡 3) j q)) w at heq
    simpa only [hderiv q, TangentSpace] using heq
  · intro q
    have hp : unitRicciKernelProjection D (j q) = i q := congrFun hproj q
    have hunit : g.inner (i q) (j q).1.snd (j q).1.snd = 1 := by
      rw [← hp]
      exact (j q).2.1
    have hnonzero : (j q).1.snd ≠ 0 := by
      intro hzero
      simp only [hzero, map_zero] at hunit
      norm_num at hunit
    have hnull : D.ricci (i q) (j q).1.snd (j q).1.snd = 0 := by
      rw [← hp]
      exact (j q).2.2 _
    rintro ⟨v, hv⟩
    apply (htrans N D hN).2.2 q (j q).1.snd hnonzero hnull
    refine ⟨v, ?_⟩
    have heq := congrArg (mfderiv (𝓡 3) (𝓡 3) (unitRicciKernelProjection D) (j q)) hv
    rw [unitRicciKernelField_projection D hc] at heq
    exact (congrArg (fun L => L v) (hderiv q)).symm.trans heq

end PoincareMT.M30
