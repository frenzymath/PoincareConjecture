import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.AnnularLengthRegularity
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.AnnularLengthArea
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.BoundaryCurveLipschitz
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.CollarGluing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Metric
open scoped Manifold ContDiff Bundle NNReal ENNReal

universe u

namespace PoincareConjecture

theorem m60Disk_regularize_of_increasing_lift
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) {gamma : C1FreeLoopSpace (M := M)}
    (D : LipschitzSpanningDisk g gamma) (H : ℝ ≃ₜ ℝ) (hH : Monotone H)
    (hperiod : ∀ t, H (t + rampPeriod) = H t + rampPeriod)
    (hlift : ∀ t : ℝ,
      (⟨Proofs.M58.angularPoint (H t), Proofs.M58.norm_angularPoint (H t)⟩ : LoopCircle) =
        D.reparameterization.map ⟨Proofs.M58.angularPoint t, Proofs.M58.norm_angularPoint t⟩) :
    ∃ D' : LipschitzSpanningDisk g gamma,
      (∀ z : LoopCircle, D'.map z = gamma z) ∧ D'.area = D.area := by
  classical
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace LoopAmbient M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle LoopAmbient (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  let f := periodicFreeLoop gamma
  have hgamma (t : ℝ) : f t =
      gamma ⟨Proofs.M58.angularPoint t, Proofs.M58.norm_angularPoint t⟩ := by
    simpa only [f, periodicFreeLoop, Proofs.M58.angularPoint] using
      gamma.boundary ⟨Proofs.M58.angularPoint t, Proofs.M58.norm_angularPoint t⟩
  obtain ⟨L, hL, hbound⟩ := m60_exists_periodicLoop_lipschitz_bound g gamma
  have hf : LipschitzWith (NNReal.mk L hL) f := by
    intro s t
    simpa +instances only [ENNReal.coe_nnreal_eq, edist_dist, Real.dist_eq] using! hbound s t
  have htrace (t : ℝ) : f (H t) = D.map (Proofs.M58.angularPoint t) := by
    calc
      f (H t) = gamma ⟨Proofs.M58.angularPoint (H t), Proofs.M58.norm_angularPoint (H t)⟩ :=
        hgamma (H t)
      _ = gamma (D.reparameterization.map
          ⟨Proofs.M58.angularPoint t, Proofs.M58.norm_angularPoint t⟩) := congrArg gamma (hlift t)
      _ = D.map (Proofs.M58.angularPoint t) := (D.boundary_eq _).symm
  have hfH : LipschitzWith (NNReal.mk D.lipschitz_constant D.lipschitz_nonnegative) (f ∘ H) := by
    intro s t
    dsimp only [Function.comp_def]
    rw [htrace, htrace]
    simpa +instances only [ENNReal.coe_nnreal_eq, edist_dist, Real.dist_eq] using!
      m60Disk_angular_trace_bound g D s t
  let ell := variationOnFromTo f univ 0
  let beta := naturalParameterization f univ 0
  let a := fun t => ell (H t)
  have hell : LipschitzWith (NNReal.mk L hL) ell :=
    lipschitzOnWith_univ.mp (M60.lipschitzOnWith_variationOnFromTo hf.lipschitzOnWith (mem_univ 0))
  have ha : LipschitzWith (NNReal.mk D.lipschitz_constant D.lipschitz_nonnegative) a :=
    M60.lipschitzWith_lengthParameter_comp_homeomorph
      hf.lipschitzOnWith.locallyBoundedVariationOn H hH hfH
  have hS : Convex ℝ (range ell) := M60.convex_range_lengthParameter hf
  have hbeta : LipschitzOnWith 1 beta (range ell) := by
    simpa only [image_univ] using
      M60.lipschitzOnWith_naturalParameterization hf.lipschitzOnWith.locallyBoundedVariationOn
        (mem_univ 0)
  have hfactor (t : ℝ) : beta (ell t) = f t :=
    edist_eq_zero.mp (edist_naturalParameterization_eq_zero
      hf.lipschitzOnWith.locallyBoundedVariationOn (mem_univ 0) (mem_univ t))
  have hellperiod (t : ℝ) : ell (t + rampPeriod) = ell t + ell rampPeriod :=
    M60.lengthParameter_add_period hf.lipschitzOnWith.locallyBoundedVariationOn
      (Proofs.M58.periodic_periodicFreeLoop gamma) t
  have haperiod (t : ℝ) : a (t + rampPeriod) = a t + ell rampPeriod := by
    dsimp only [a]
    rw [hperiod, hellperiod]
  have hbperiod (s : ℝ) (hs : s ∈ range ell) : beta (s + ell rampPeriod) = beta s :=
    M60.naturalParameterization_add_periodLength hf.lipschitzOnWith.locallyBoundedVariationOn
      (Proofs.M58.periodic_periodicFreeLoop gamma) hs
  have haS (t : ℝ) : a t ∈ range ell := mem_range_self (H t)
  have hellS (t : ℝ) : ell t ∈ range ell := mem_range_self t
  have hp (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : Function.Periodic
      (fun t => beta (M60.lengthParameterInterpolation a ell (u, t))) rampPeriod :=
    M60.periodic_lengthParameterInterpolation hS haS hellS haperiod hellperiod hbperiod hu
  let F := m60AnnularLengthMap beta a ell
  obtain ⟨K, hK⟩ := m60AnnularLengthMap_lipschitz ha hell hS haS hellS hbeta hp
  have hLip : ∀ x ∈ loopDiskSet ∩ {z | (1 / 2 : ℝ) ≤ ‖z‖},
      ∀ y ∈ loopDiskSet ∩ {z | (1 / 2 : ℝ) ≤ ‖z‖},
      g.edist (F x) (F y) ≤ ENNReal.ofReal (K : ℝ) * ENNReal.ofReal ‖x - y‖ := by
    intro x hx y hy
    have hx' : 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 :=
      ⟨hx.2, by simpa only [loopDiskSet, mem_closedBall, dist_zero_right] using hx.1⟩
    have hy' : 1 / 2 ≤ ‖y‖ ∧ ‖y‖ ≤ 1 :=
      ⟨hy.2, by simpa only [loopDiskSet, mem_closedBall, dist_zero_right] using hy.1⟩
    simpa +instances only [ENNReal.ofReal_coe_nnreal, edist_dist, dist_eq_norm] using! hK hx' hy'
  obtain ⟨harea, hzero⟩ := m60AnnularLengthMap_area_zero g ha hell hS haS hellS
    (C := 1) (fun s hs t ht => by
      simpa +instances only [edist_dist, Real.dist_eq] using! hbeta hs ht) hp
  change (∫ z in (closedBall (0 : LoopPlane) (1 / 2))ᶜ ∩ loopDiskSet,
    m60AreaDensity g F z) = 0 at hzero
  have hinner (t : ℝ) : F ((1 / 2 : ℝ) • Proofs.M58.angularPoint t) =
      D.map (Proofs.M58.angularPoint t) :=
    (m60AnnularLengthMap_traces hp t).1.trans ((hfactor (H t)).trans (htrace t))
  have houter (t : ℝ) : F (Proofs.M58.angularPoint t) =
      gamma ⟨Proofs.M58.angularPoint t, Proofs.M58.norm_angularPoint t⟩ :=
    (m60AnnularLengthMap_traces hp t).2.trans ((hfactor t).trans (hgamma t))
  have hmatch (z : LoopPlane) (hz : ‖z‖ = 1 / 2) :
      D.map ((1 / 2 : ℝ)⁻¹ • z) = F z := by
    have heq : (1 / 2 : ℝ) • Proofs.M58.angularPoint (m60PlaneAngle z) = z :=
      hz ▸ m60PlaneAngle_polar z
    rw [← heq, smul_smul]
    norm_num only [inv_div, div_one, mul_one_div_cancel, one_smul]
    exact (hinner _).symm
  have hboundary (z : LoopCircle) : F z = gamma z := by
    have hz : Proofs.M58.angularPoint (m60PlaneAngle z) = (z : LoopPlane) := by
      simpa only [z.property, one_smul] using m60PlaneAngle_polar (z : LoopPlane)
    have hh := houter (m60PlaneAngle z)
    exact (congrArg F hz).symm.trans (hh.trans (congrArg gamma (Subtype.ext hz)))
  let sigma : CircleReparameterization := {
    map := id
    inverse := id
    left_inverse := fun _ => rfl
    right_inverse := fun _ => rfl
    continuous_map := continuous_id
    continuous_inverse := continuous_id }
  obtain ⟨D', hmap, harea'⟩ := m60DiskGluing_of_collar g D
    (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num) F sigma hmatch hboundary K.property hLip harea
  refine ⟨D', ?_, ?_⟩
  · intro z
    have hz : (z : LoopPlane) ∉ closedBall (0 : LoopPlane) (1 / 2 : ℝ) := by
      simp only [mem_closedBall, dist_zero_right, z.property]
      norm_num
    rw [hmap, piecewise_eq_of_notMem _ _ _ hz]
    exact hboundary z
  · simpa only [hzero, add_zero] using harea'

end PoincareConjecture
