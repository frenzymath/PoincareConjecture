import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.Cylinder.AngularCollar
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.AngularCollar
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Vertical

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.EpsilonNeck

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

private theorem coordinate_map_mfderiv_injective
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g)
    {z : RoundCylinderSpace} (hz : z ∈ N.cylinderDomain) :
    Function.Injective (mfderiv CylModel (𝓡 3) N.coordinate_map z) := by
  have hh := mfderiv_comp z
    ((N.coordinate_inverse_smooth.contMDiffAt
      (N.carrier_open.mem_nhds (N.coordinate_map_mem hz))).mdifferentiableAt (by simp))
    ((N.coordinate_map_smooth.contMDiffAt
      (N.cylinderDomain_open.mem_nhds hz)).mdifferentiableAt (by simp))
  have heq : N.coordinate_inverse ∘ N.coordinate_map =ᶠ[𝓝 z] id := by
    filter_upwards [N.cylinderDomain_open.mem_nhds hz] with w hw
    exact N.coordinate_inverse_coordinate_map hw
  rw [heq.mfderiv_eq, mfderiv_id] at hh
  have hleft (v : TangentSpace CylModel z) :
      mfderiv (𝓡 3) CylModel N.coordinate_inverse (N.coordinate_map z)
        (mfderiv CylModel (𝓡 3) N.coordinate_map z v) = v :=
    (congrArg (fun L => L v) hh).symm
  intro v w hvw
  rw [← hleft v, ← hleft w, hvw]

theorem normalized_collar_of_epsilon_le :
    ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} (A B : EpsilonNeck g),
        A.epsilon ≤ 1 / 200 → B.epsilon ≤ 1 / 200 →
        ∀ s ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹,
        (∀ q : UnitTwoSphere, B.coordinate_map (q, s) ∈ A.carrier) →
        ∃ (r : ℝ) (D : Diffeomorph CylModel CylModel
            RoundCylinderSpace RoundCylinderSpace ∞)
          (F : RoundCylinderSpace → RoundCylinderSpace),
          0 < r ∧ ContMDiff CylModel CylModel ∞ F ∧
          (∀ p : RoundCylinderSpace, (D p).2 = p.2) ∧
          (∀ p : RoundCylinderSpace, (F p).1 = p.1) ∧
          (∀ p : RoundCylinderSpace, F p ∈ A.cylinderDomain) ∧
          (∀ q : UnitTwoSphere, deriv (fun t : ℝ => (F (q, t)).2) 0 ≠ 0) ∧
          ∀ t : ℝ, |t| < r →
            s + t ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹ ∧
            (∀ q : UnitTwoSphere, B.coordinate_map (q, s + t) ∈ A.carrier) ∧
            ∀ q : UnitTwoSphere, F (q, t) =
              A.coordinate_inverse (B.coordinate_map ((D.symm (q, t)).1, s + t)) := by
  intro M _ _ _ _ _ _ _ g A B hA hB s hs hc
  obtain ⟨R, D, hR, hDheight, hDinner⟩ := angular_collar_extension_of_epsilon_le A B hA hB s hs hc
  let r := R / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hrR : 2 * r < R := by dsimp [r]; linarith
  let b : ContDiffBump (0 : ℝ) := ⟨r, 2 * r, hr, by linarith⟩
  let σ : ℝ → ℝ := fun t => t * b t
  have hσ : ContDiff ℝ ∞ σ := contDiff_id.mul b.contDiff
  have hσinner (t : ℝ) (ht : |t| < r) : σ t = t := by
    have hb : b t = 1 := b.one_of_mem_closedBall
      (by simpa [Metric.mem_closedBall, Real.dist_eq] using ht.le)
    simp only [σ, hb, mul_one]
  have hσbound (t : ℝ) : |σ t| < R := by
    by_cases ht : |t| < 2 * r
    · have hle : |σ t| ≤ |t| := by
        dsimp [σ]
        rw [abs_mul, abs_of_nonneg b.nonneg]
        nlinarith [b.le_one (x := t), abs_nonneg t]
      exact hle.trans_lt (ht.trans hrR)
    · have hb : b t = 0 := b.zero_of_le_dist
        (by simpa [Real.dist_eq] using le_of_not_gt ht)
      simpa [σ, hb] using hR
  have hDinvheight (p : RoundCylinderSpace) : (D.symm p).2 = p.2 := by
    simpa only [D.apply_symm_apply] using (hDheight (D.symm p)).symm
  have hbound (t : ℝ) := (hDinner (σ t) (hσbound t)).1
  have hcont (t : ℝ) := (hDinner (σ t) (hσbound t)).2.1
  have hagree (t : ℝ) := (hDinner (σ t) (hσbound t)).2.2
  let S : RoundCylinderSpace → RoundCylinderSpace := fun p => (p.1, σ p.2)
  have hS : ContMDiff CylModel CylModel ∞ S :=
    contMDiff_fst.prodMk (hσ.contMDiff.comp contMDiff_snd)
  let bp : RoundCylinderSpace → RoundCylinderSpace :=
    fun p => ((D.symm (S p)).1, s + σ p.2)
  have hbp : ContMDiff CylModel CylModel ∞ bp :=
    (contMDiff_fst.comp (D.symm.contMDiff.comp hS)).prodMk
      (contMDiff_const.add (hσ.contMDiff.comp contMDiff_snd))
  have hbp_mem (p : RoundCylinderSpace) : bp p ∈ B.cylinderDomain :=
    ⟨mem_univ _, hbound p.2⟩
  have hBmem (p : RoundCylinderSpace) : B.coordinate_map (bp p) ∈ A.carrier :=
    hcont p.2 (D.symm (S p)).1
  have hB : ContMDiff CylModel (𝓡 3) ∞ (fun p => B.coordinate_map (bp p)) := by
    intro p
    exact (B.coordinate_map_smooth.contMDiffAt
      (B.cylinderDomain_open.mem_nhds (hbp_mem p))).comp p hbp.contMDiffAt
  let F : RoundCylinderSpace → RoundCylinderSpace :=
    fun p => A.coordinate_inverse (B.coordinate_map (bp p))
  have hF : ContMDiff CylModel CylModel ∞ F := by
    intro p
    exact (A.coordinate_inverse_smooth.contMDiffAt
      (A.carrier_open.mem_nhds (hBmem p))).comp p hB.contMDiffAt
  have hFangular (p : RoundCylinderSpace) : (F p).1 = p.1 := by
    have hh := hagree p.2 (D.symm (S p)).1
    have hpair : ((D.symm (S p)).1, σ p.2) = D.symm (S p) :=
      Prod.ext rfl (hDinvheight (S p)).symm
    rw [hpair, D.apply_symm_apply] at hh
    exact hh.symm
  refine ⟨r, D, F, hr, hF, hDheight, hFangular,
    (fun p => A.coordinate_inverse_mem _ (hBmem p)), ?_, ?_⟩
  · intro q
    apply CylinderGluing.axial_deriv_ne_zero_of_mfderiv_injective F hF hFangular (q, 0)
    let T : Diffeomorph CylModel CylModel RoundCylinderSpace RoundCylinderSpace ∞ :=
      { toEquiv := (Equiv.refl UnitTwoSphere).prodCongr (Equiv.addLeft s)
        contMDiff_toFun := contMDiff_fst.prodMk (contMDiff_const.add contMDiff_snd)
        contMDiff_invFun := contMDiff_fst.prodMk (contMDiff_const.add contMDiff_snd) }
    have hbp_eq : bp = fun p => T (D.symm (S p)) := by
      funext p
      exact Prod.ext rfl (congrArg (s + ·) (hDinvheight (S p))).symm
    have hSe : S =ᶠ[𝓝 (q, (0 : ℝ))] id := by
      have hn : {p : RoundCylinderSpace | |p.2| < r} ∈ 𝓝 (q, (0 : ℝ)) :=
        (isOpen_lt continuous_snd.abs continuous_const).mem_nhds (by simpa using hr)
      filter_upwards [hn] with p hp
      exact Prod.ext rfl (hσinner p.2 hp)
    have hbpinj : Function.Injective (mfderiv CylModel CylModel bp (q, 0)) := by
      rw [hbp_eq]
      have heq : (fun p => T (D.symm (S p))) =ᶠ[𝓝 (q, (0 : ℝ))]
          fun p => T (D.symm p) := hSe.fun_comp (fun p => T (D.symm p))
      rw [heq.mfderiv_eq]
      exact ((D.symm.trans T).mfderivToContinuousLinearEquiv (by simp) (q, 0)).injective
    have hBinj : Function.Injective
        (mfderiv CylModel (𝓡 3) (fun p => B.coordinate_map (bp p)) (q, 0)) := by
      change Function.Injective (mfderiv CylModel (𝓡 3) (B.coordinate_map ∘ bp) (q, 0))
      rw [mfderiv_comp (q, (0 : ℝ))
        ((B.coordinate_map_smooth.contMDiffAt
          (B.cylinderDomain_open.mem_nhds (hbp_mem (q, 0)))).mdifferentiableAt (by simp))
        (hbp.mdifferentiableAt (by simp))]
      exact (coordinate_map_mfderiv_injective B (hbp_mem (q, 0))).comp hbpinj
    have hAinj : Function.Injective (mfderiv (𝓡 3) CylModel A.coordinate_inverse
        (B.coordinate_map (bp (q, 0)))) := by
      intro v w hvw
      have hv := A.coordinate_map_mfderiv_inverse_prod (hBmem (q, 0)) v
      have hw := A.coordinate_map_mfderiv_inverse_prod (hBmem (q, 0)) w
      rw [← hv, ← hw, hvw]
    change Function.Injective (mfderiv CylModel CylModel
      (A.coordinate_inverse ∘ (fun p => B.coordinate_map (bp p))) (q, 0))
    rw [mfderiv_comp (q, (0 : ℝ))
      ((A.coordinate_inverse_smooth.contMDiffAt
        (A.carrier_open.mem_nhds (hBmem (q, 0)))).mdifferentiableAt (by simp))
      (hB.mdifferentiableAt (by simp))]
    exact hAinj.comp hBinj
  · intro t ht
    refine ⟨?_, ?_, ?_⟩
    · simpa only [hσinner t ht] using hbound t
    · intro q
      simpa only [hσinner t ht] using hcont t q
    · intro q
      simp only [F, bp, S, hσinner t ht]

end PoincareConjecture.EpsilonNeck
