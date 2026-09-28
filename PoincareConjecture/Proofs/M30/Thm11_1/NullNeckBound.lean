import PoincareConjecture.Proofs.M30.Thm11_1.StaticNullCover
import PoincareConjecture.Proofs.M30.Thm11_1.NullCoverFlow
import PoincareConjecture.Proofs.M30.Thm11_1.LiftedNeckSphere
import PoincareConjecture.Proofs.M30.Thm11_1.CompactFlowoutBound
import PoincareConjecture.Proofs.M30.Thm5_33.CurvatureNorm
import Mathlib.Algebra.Order.Archimedean.Real.Basic

















set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set PoincareConjecture.RicciFlow.Splitting
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M30




theorem exists_neck_scalar_and_curvature_bound_of_local_parallel_null_sections :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T3Space M] [PreconnectedSpace M] {g : RiemannianMetric 3 M},
      ∀ (D : LeviCivitaData g), D.CurvatureTensorCalculus →
        MetricComplete g → D.NonnegativeSectionalCurvature →
        (∀ x : M, ricciNullity D x = 1) →
        (∀ p : UnitRicciKernel D,
          ∃ (U : Set M) (V : (y : M) → TangentSpace (𝓡 3) y),
            IsOpen U ∧ p.1.proj ∈ U ∧
            ContMDiffOn (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞ (T% V) U ∧
            V p.1.proj = p.1.snd ∧
            ∀ y ∈ U, g.inner y (V y) (V y) = 1 ∧
              (∀ w : TangentSpace (𝓡 3) y, D.ricci y (V y) w = 0) ∧
              ∀ w : TangentSpace (𝓡 3) y, D.connection V y w = 0) →
        ∀ N : EpsilonNeck g, N.epsilon ≤ epsilon0 →
          ∃ B : ℝ, 0 < B ∧ (∀ x : M, |D.scalarCurvature x| ≤ B) ∧
            ∀ x : M, |D.curvatureTensorNorm x| ≤ 13 * B := by
  classical
  obtain ⟨epsilon0, hepsilon0, hsmall, hlift⟩ :=
    exists_neck_lifted_sphere_transverse_unitRicciKernelField.{u}
  refine ⟨epsilon0, hepsilon0, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g D hD hcomplete hsec hdim hlocal N hN
  let : T25Space M := T3Space.t25Space
  let : T2Space M := T25Space.t2Space
  have hsections (x : M) :
      ∃ (U : Set M) (V : (y : M) → TangentSpace (𝓡 3) y),
        IsOpen U ∧ x ∈ U ∧
        ContMDiffOn (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞ (T% V) U ∧
        ∀ y ∈ U, g.inner y (V y) (V y) = 1 ∧
          ∀ w : TangentSpace (𝓡 3) y, D.ricci y (V y) w = 0 := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let : FiniteDimensional ℝ (TangentSpace (𝓡 3) x) := by
      unfold TangentSpace
      infer_instance
    obtain ⟨z, hz⟩ := Module.finrank_pos_iff_exists_ne_zero.mp
      (show 0 < ricciNullity D x by rw [hdim]; norm_num)
    have hz' : (z : TangentSpace (𝓡 3) x) ≠ 0 := fun he => hz (Subtype.ext he)
    let q := g.inner x z z
    have hq : 0 < q := g.pos x z hz'
    let v : TangentSpace (𝓡 3) x := (Real.sqrt q)⁻¹ • (z : TangentSpace (𝓡 3) x)
    have hv : ∀ w, D.ricci x v w = 0 :=
      (mem_ricciKernel _ _ _).mp ((ricciKernel D x).smul_mem _ z.property)
    have hu : g.inner x v v = 1 := by
      simp only [v, map_smul, smul_apply, smul_eq_mul]
      change (Real.sqrt q)⁻¹ * ((Real.sqrt q)⁻¹ * q) = 1
      field_simp [(Real.sqrt_pos.mpr hq).ne']
      exact (Real.sq_sqrt hq.le).symm
    let p : UnitRicciKernel D := ⟨⟨x, v⟩, hu, hv⟩
    obtain ⟨U, V, hU, hx, hV, _, hn⟩ := hlocal p
    exact ⟨U, V, hU, hx, hV, fun y hy => ⟨(hn y hy).1, (hn y hy).2.1⟩⟩
  obtain ⟨hc, hcard⟩ := unitRicciKernel_doubleCover_of_local_unit_sections g D hdim hsections
  let := unitRicciKernelChartedSpace D hc
  let := unitRicciKernelIsManifold D hc
  let gQ := unitRicciKernelMetric D hc
  let X := unitRicciKernelField D hc
  obtain ⟨Phi, hs, hcurve, h0, hact, hmetric⟩ :=
    exists_unitRicciKernel_isometric_globalFlow_of_local_parallel_sections
      D hc hcard hcomplete hdim hlocal
  obtain ⟨j, hj, _, hj_inj, htrans⟩ := hlift N D hN hc hcard
  let : Nonempty UnitTwoSphere := ⟨(N.coordinate_inverse N.center).1⟩
  have hpi := unitRicciKernelProjection_isLocalDiffeomorph D hc
  obtain ⟨B, hB, hR⟩ := scalar_bounded_of_compact_transverse_isometric_flowout
    (n := 2) gQ g D hcomplete (unitRicciKernelProjection D) hpi.contMDiff
    (fun _ _ _ => rfl) j hj hj_inj X Phi hs hcurve h0 hact hmetric htrans
  refine ⟨B, hB, hR, ?_⟩
  intro x
  have hleast : 0 ≤ D.leastSectionalCurvature x := by
    apply Real.sInf_nonneg
    rintro k ⟨v, w, _, rfl⟩
    exact hsec x v w
  have hdefect : D.negativeCurvaturePart x = 0 :=
    max_eq_right (neg_nonpos.mpr hleast)
  exact curvatureTensorNorm_le_of_scalar_negativeDefect_le D hD x hB.le
    ((le_abs_self _).trans (hR x)) (hdefect.trans_le hB.le)

end PoincareConjecture.M30
