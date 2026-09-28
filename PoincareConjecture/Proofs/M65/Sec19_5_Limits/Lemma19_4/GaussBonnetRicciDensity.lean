import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetMinimalDiskPotential
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.ConformalRicci
import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.IntrinsicRicciTrace
import PoincareConjecture.Proofs.M04.CurvatureCalculus
import PoincareConjecture.Proofs.M04.CurvatureEnergyBochner












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff Manifold Bundle

namespace PoincareConjecture.M65MinimalDisk

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {connection : LeviCivitaData g}
  {gamma : C1FreeLoopSpace (M := M)}




theorem interior_areaGram (S : M65MinimalDisk g connection gamma)
    {z : LoopPlane} (hz : z ∈ ball (0 : LoopPlane) 1) :
    m60AreaGram g S.disk.map z = S.conformalFactor z • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  have hh := S.boundaryColumn_inner (ball_subset_closedBall hz) i j
  simpa only [S.boundaryColumn_eq_mfderiv hz, m60AreaGram, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero] using hh

private theorem interior_ricci_continuousOn (S : M65MinimalDisk g connection gamma)
    (i : Fin 2) :
    ContinuousOn (fun z => connection.ricci (S.disk.map z)
      (mfderiv (𝓡 2) (𝓡 3) S.disk.map z (EuclideanSpace.basisFun (Fin 2) ℝ i))
      (mfderiv (𝓡 2) (𝓡 3) S.disk.map z (EuclideanSpace.basisFun (Fin 2) ℝ i)))
        (ball (0 : LoopPlane) 1) := by
  let v := EuclideanSpace.basisFun (Fin 2) ℝ i
  let V := fun z => mfderiv (𝓡 2) (𝓡 3) S.disk.map z v
  have hmodel : ContMDiff ((𝓡 2).prod (𝓡 2)) ((𝓡 2).prod (𝓡 2)) ∞
      (fun z : LoopPlane × LoopPlane => (⟨z.1, z.2⟩ : TangentBundle (𝓡 2) LoopPlane)) := by
    convert! (contMDiff_tangentBundleModelSpaceHomeomorph_symm (I := 𝓡 2) (n := ∞)) using 1
    rw [chartedSpaceSelf_prod]
    rfl
  have hpre : ContMDiff (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞
      (fun z => (⟨z, v⟩ : TangentBundle (𝓡 2) LoopPlane)) :=
    hmodel.comp (contMDiff_id.prodMk contMDiff_const)
  have hwithin := S.interior_smooth.contMDiffOn_tangentMapWithin
    (m := ∞) (by simp) isOpen_ball.uniqueMDiffOn
  have hcol : ContMDiffOn (𝓡 2) ((𝓡 3).prod (𝓡 3)) ∞
      (fun z => (⟨S.disk.map z, V z⟩ : TangentBundle (𝓡 3) M))
        (ball (0 : LoopPlane) 1) := by
    apply (hwithin.comp hpre.contMDiffOn (fun _ hz => hz)).congr
    intro z hz
    simp only [Function.comp_apply, tangentMapWithin, V,
      mfderivWithin_of_mem_nhds (isOpen_ball.mem_nhds hz)]
  intro z hz
  have hh := M60.contMDiffAt_tensorEvaluation_along
    (M04.isSmoothCovariantTensor_ricciEvaluation connection)
    (S.interior_smooth.contMDiffAt (isOpen_ball.mem_nhds hz))
    (fun _ : Fin 2 => V) (fun _ => hcol.contMDiffAt (isOpen_ball.mem_nhds hz))
  exact hh.continuousAt.continuousWithinAt

set_option maxHeartbeats 1600000 in




theorem gaussContraction_integrable (S : M65MinimalDisk g connection gamma) :
    IntegrableOn (fun z => m65PlaneRicciTraceDensity connection S.disk.map z -
      connection.scalarCurvature (S.disk.map z) * m60AreaDensity g S.disk.map z / 2)
        loopDiskSet volume := by
  classical
  let Q := fun z => m65PlaneRicciTraceDensity connection S.disk.map z -
    connection.scalarCurvature (S.disk.map z) * m60AreaDensity g S.disk.map z / 2
  let U := ball (0 : LoopPlane) 1
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  have hcalc := connection.curvatureTensorCalculus
  have hscalar := (m60ScalarCurvature_contMDiff connection hcalc).continuous
  have hnorm : Continuous connection.ricciNormSq := by
    simpa only [m60Ricci_tensorNorm_sq] using
      (M04.contMDiff_tensorNorm_sq g (M04.isSmoothCovariantTensor_ricciEvaluation
        connection)).continuous
  have hK : IsCompact (S.disk.map '' loopDiskSet) :=
    (isCompact_closedBall (0 : LoopPlane) 1).image_of_continuousOn
      S.boundary_regular.continuousOn
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn hnorm.continuousOn
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hscalar.continuousOn
  let C := max A 1
  let D := max B 0
  have hC : 0 ≤ C := le_trans zero_le_one (le_max_right _ _)
  have hD : 0 ≤ D := le_max_right _ _
  have hRic (z : LoopPlane) (hz : z ∈ loopDiskSet)
      (v : TangentSpace (𝓡 3) (S.disk.map z)) :
      |connection.ricci (S.disk.map z) v v| ≤ C * g.inner (S.disk.map z) v v := by
    apply m60Ricci_quadratic_bound connection hcalc _ hC
    have hbound := (le_abs_self (connection.ricciNormSq (S.disk.map z))).trans
      (hA _ ⟨z, hz, rfl⟩)
    have hAC : A ≤ C := le_max_left _ _
    have hC1 : 1 ≤ C := le_max_right _ _
    nlinarith
  have hSc (z : LoopPlane) (hz : z ∈ loopDiskSet) :
      |connection.scalarCurvature (S.disk.map z)| ≤ D :=
    (hB _ ⟨z, hz, rfl⟩).trans (le_max_left _ _)
  have hQeq (z : LoopPlane) (hz : z ∈ U) : Q z =
      (∑ i : Fin 2, connection.ricci (S.disk.map z)
        (mfderiv (𝓡 2) (𝓡 3) S.disk.map z (e i))
        (mfderiv (𝓡 2) (𝓡 3) S.disk.map z (e i))) -
      connection.scalarCurvature (S.disk.map z) * S.conformalFactor z / 2 := by
    dsimp only [Q]
    rw [m65PlaneRicciTraceDensity_eq_sum_of_conformal connection S.disk.map z
      (S.conformalFactor z) (S.interior_areaGram hz),
      m65AreaDensity_eq_of_conformal g S.disk.map z (S.conformalFactor z)
        (S.interior_areaGram hz)]
  have hcont : ContinuousOn Q U := by
    apply ((continuousOn_finsetSum Finset.univ (fun i _ => S.interior_ricci_continuousOn i)).sub
      (((hscalar.comp_continuousOn S.interior_smooth.continuousOn).mul
        (S.conformalFactor_continuousOn.mono ball_subset_closedBall)).div_const 2)).congr
    intro z hz
    exact hQeq z hz
  have hbound (z : LoopPlane) (hz : z ∈ U) :
      ‖Q z‖ ≤ (2 * C + D / 2) * S.conformalFactor z := by
    have hzK := ball_subset_closedBall hz
    have hcol (i : Fin 2) : g.inner (S.disk.map z)
        (mfderiv (𝓡 2) (𝓡 3) S.disk.map z (e i))
        (mfderiv (𝓡 2) (𝓡 3) S.disk.map z (e i)) = S.conformalFactor z := by
      simpa only [S.boundaryColumn_eq_mfderiv hz, ite_true, e] using
        S.boundaryColumn_inner hzK i i
    have h0 := hRic z hzK (mfderiv (𝓡 2) (𝓡 3) S.disk.map z (e 0))
    have h1 := hRic z hzK (mfderiv (𝓡 2) (𝓡 3) S.disk.map z (e 1))
    rw [hcol] at h0 h1
    rw [hQeq z hz, Fin.sum_univ_two, Real.norm_eq_abs]
    calc
      _ ≤ |connection.ricci (S.disk.map z)
          (mfderiv (𝓡 2) (𝓡 3) S.disk.map z (e 0))
          (mfderiv (𝓡 2) (𝓡 3) S.disk.map z (e 0))| +
          |connection.ricci (S.disk.map z)
          (mfderiv (𝓡 2) (𝓡 3) S.disk.map z (e 1))
          (mfderiv (𝓡 2) (𝓡 3) S.disk.map z (e 1))| +
          |connection.scalarCurvature (S.disk.map z) * S.conformalFactor z / 2| :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ C * S.conformalFactor z + C * S.conformalFactor z +
          D * S.conformalFactor z / 2 := by
        rw [abs_div, abs_mul, abs_of_nonneg (S.conformalFactor_nonneg z),
          abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        exact add_le_add (add_le_add h0 h1)
          (div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hSc z hzK) (S.conformalFactor_nonneg z))
            (by norm_num))
      _ = _ := by ring
  have hInt : IntegrableOn S.conformalFactor U volume :=
    (S.conformalFactor_continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : LoopPlane) 1)).mono_set ball_subset_closedBall
  have hQU : IntegrableOn Q U volume :=
    (hInt.const_mul (2 * C + D / 2)).mono' (hcont.aestronglyMeasurable isOpen_ball.measurableSet)
      ((ae_restrict_mem isOpen_ball.measurableSet).mono fun z hz => hbound z hz)
  have heq : loopDiskSet =ᵐ[volume] U := by
    have hnull : ∀ᵐ z : LoopPlane ∂volume, z ∉ sphere (0 : LoopPlane) 1 := by
      rw [ae_iff]
      simpa only [not_not, Set.ofPred_mem_eq] using
        Measure.addHaar_sphere volume (0 : LoopPlane) 1
    filter_upwards [hnull] with z hz
    apply propext
    constructor
    · intro hK
      exact mem_ball_zero_iff.mpr (lt_of_le_of_ne (mem_closedBall_zero_iff.mp hK)
        (by simpa only [mem_sphere_zero_iff_norm] using hz))
    · intro hzU
      exact ball_subset_closedBall hzU
  change Integrable Q (volume.restrict loopDiskSet)
  rw [Measure.restrict_congr_set heq]
  exact hQU

end PoincareConjecture.M65MinimalDisk
