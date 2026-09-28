import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Fibration.Quotient.Collars.Scalar
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Fibration.Quotient.Collars.Angular
import Mathlib.Analysis.Normed.Operator.Banach

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.CylinderGluing

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

private theorem tangentCoordChange_bijective {x y z : UnitTwoSphere}
    (hx : z ∈ (extChartAt (𝓡 2) x).source)
    (hy : z ∈ (extChartAt (𝓡 2) y).source) :
    Function.Bijective (tangentCoordChange (𝓡 2) x y z) := by
  have hleft : Function.LeftInverse (tangentCoordChange (𝓡 2) y x z)
      (tangentCoordChange (𝓡 2) x y z) := by
    intro v
    rw [tangentCoordChange_comp ⟨⟨hx, hy⟩, hx⟩, tangentCoordChange_self hx]
  have hright : Function.RightInverse (tangentCoordChange (𝓡 2) y x z)
      (tangentCoordChange (𝓡 2) x y z) := by
    intro v
    rw [tangentCoordChange_comp ⟨⟨hy, hx⟩, hy⟩, tangentCoordChange_self hy]
  exact ⟨hleft.injective, hright.surjective⟩

theorem eventually_bijective_slice_mfderiv
    (f : RoundCylinderSpace → UnitTwoSphere) (p : RoundCylinderSpace)
    (hf : ContMDiffAt CylModel (𝓡 2) ∞ f p)
    (hbij : Function.Bijective (mfderiv (𝓡 2) (𝓡 2) (fun q => f (q, p.2)) p.1)) :
    ∀ᶠ z : RoundCylinderSpace in 𝓝 p,
      Function.Bijective (mfderiv (𝓡 2) (𝓡 2) (fun q => f (q, z.2)) z.1) := by
  let a : RoundCylinderSpace → UnitTwoSphere → UnitTwoSphere := fun z q => f (q, z.2)
  let D : RoundCylinderSpace → EuclideanSpace ℝ (Fin 2) →L[ℝ]
      EuclideanSpace ℝ (Fin 2) :=
    fun z : RoundCylinderSpace => mfderiv (𝓡 2) (𝓡 2) (a z) z.1
  let A := inTangentCoordinates (𝓡 2) (𝓡 2) Prod.fst f D p
  have ha : ContMDiffAt ((CylModel).prod (𝓡 2)) (𝓡 2) ∞
      (Function.uncurry a) (p, p.1) :=
    hf.comp (p, p.1) (contMDiffAt_snd.prodMk (contMDiffAt_snd.comp _ contMDiffAt_fst))
  have hA : ContinuousAt A p := by
    simpa only [A, D, a, Prod.eta] using
      (ha.mfderiv a Prod.fst contMDiffAt_fst (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)).continuousAt
  have hAp : A p = D p := by
    dsimp only [A]
    rw [inTangentCoordinates_eq _ _ _ (mem_chart_source _ _) (mem_chart_source _ _)]
    apply ContinuousLinearMap.ext
    intro v
    change tangentCoordChange (𝓡 2) (f p) (f p) (f p)
      (D p (tangentCoordChange (𝓡 2) p.1 p.1 p.1 v)) = D p v
    rw [tangentCoordChange_self (mem_extChartAt_source _),
      tangentCoordChange_self (mem_extChartAt_source _)]
  have hunit : IsUnit (A p) := by
    rw [hAp]
    exact ContinuousLinearMap.isUnit_iff_bijective.mpr hbij
  have hnear : ∀ᶠ z in 𝓝 p, IsUnit (A z) :=
    hA.eventually (Units.isOpen.mem_nhds hunit)
  have hx : ∀ᶠ z : RoundCylinderSpace in 𝓝 p,
      z.1 ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) p.1).source :=
    continuousAt_fst.preimage_mem_nhds ((chartAt _ p.1).open_source.mem_nhds
      (mem_chart_source _ _))
  have hy : ∀ᶠ z : RoundCylinderSpace in 𝓝 p,
      f z ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) (f p)).source :=
    hf.continuousAt.preimage_mem_nhds ((chartAt _ (f p)).open_source.mem_nhds
      (mem_chart_source _ _))
  filter_upwards [hnear, hx, hy] with z hz hzx hzy
  have hzbij := ContinuousLinearMap.isUnit_iff_bijective.mp hz
  have hright := tangentCoordChange_bijective (x := p.1) (y := z.1)
    (by simpa only [extChartAt_source] using hzx) (mem_extChartAt_source _)
  have hcoord : A z =
      (tangentCoordChange (𝓡 2) (f z) (f p) (f z)).comp
        ((D z).comp (tangentCoordChange (𝓡 2) p.1 z.1 z.1)) :=
    inTangentCoordinates_eq _ _ _ hzx hzy
  have hinj : Function.Injective (D z) := by
    intro v w hvw
    obtain ⟨v', rfl⟩ := hright.2 v
    obtain ⟨w', rfl⟩ := hright.2 w
    have heq : A z v' = A z w' := by
      rw [hcoord]
      exact congrArg (tangentCoordChange (𝓡 2) (f z) (f p) (f z)) hvw
    exact congrArg _ (hzbij.1 heq)
  exact ⟨hinj, (LinearMap.injective_iff_surjective (f := (D z).toLinearMap)).mp hinj⟩

theorem exists_supported_angular_germ_extension
    (f : RoundCylinderSpace → UnitTwoSphere) (U : Set RoundCylinderSpace)
    (hU : IsOpen U) (hf : ContMDiffOn CylModel (𝓡 2) ∞ f U)
    (e : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞)
    (hUzero : ∀ q : UnitTwoSphere, (q, (0 : ℝ)) ∈ U)
    (hzero : ∀ q : UnitTwoSphere, f (q, 0) = e q)
    (R : ℝ) (hR : 0 < R) :
    ∃ (r : ℝ) (D : Diffeomorph CylModel CylModel
        RoundCylinderSpace RoundCylinderSpace ∞),
      0 < r ∧ r < R ∧
      (∀ p : RoundCylinderSpace, (D p).2 = p.2) ∧
      (∀ p : RoundCylinderSpace, |p.2| < r → p ∈ U ∧ D p = (f p, p.2)) ∧
      (∀ p : RoundCylinderSpace, R ≤ |p.2| → D p = (e p.1, p.2)) := by
  let W : Set RoundCylinderSpace :=
    {p | p ∈ U ∧ Function.Bijective (mfderiv (𝓡 2) (𝓡 2) (fun q => f (q, p.2)) p.1)}
  have hW : IsOpen W := by
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    exact Filter.inter_mem (hU.mem_nhds hp.1)
      (eventually_bijective_slice_mfderiv f p (hf.contMDiffAt (hU.mem_nhds hp.1)) hp.2)
  have hWzero : (univ : Set UnitTwoSphere) ×ˢ ({0} : Set ℝ) ⊆ W := by
    rintro ⟨q, t⟩ ⟨_, ht⟩
    have ht0 : t = 0 := ht
    subst t
    refine ⟨hUzero q, ?_⟩
    have heq : (fun q => f (q, 0)) = e := funext hzero
    change Function.Bijective (mfderiv (𝓡 2) (𝓡 2) (fun q => f (q, 0)) q)
    rw [heq]
    exact (e.mfderivToContinuousLinearEquiv (by simp) q).bijective
  obtain ⟨u, v, _, hv, hu, hz, huv⟩ := generalized_tube_lemma
    (isCompact_univ : IsCompact (univ : Set UnitTwoSphere))
    (isCompact_singleton : IsCompact ({0} : Set ℝ)) hW hWzero
  obtain ⟨d, hd, hdv⟩ := Metric.isOpen_iff.mp hv 0 (hz (by simp))
  have hdW (q : UnitTwoSphere) (t : ℝ) (ht : |t| < d) : (q, t) ∈ W :=
    huv ⟨hu (mem_univ q), hdv (by simpa [Metric.mem_ball, Real.dist_eq] using ht)⟩
  have hslice (t : ℝ) (ht : |t| < d) :
      ∃ E : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞,
        ∀ q, E q = f (q, t) := by
    have hft : ContMDiff (𝓡 2) (𝓡 2) ∞ (fun q => f (q, t)) := by
      intro q
      exact (hf.contMDiffAt (hU.mem_nhds (hdW q t ht).1)).comp q
        (contMDiff_id.prodMk contMDiff_const).contMDiffAt
    have hlocal := Poincare.isLocalDiffeomorph_of_contMDiff_bijective_mfderiv
      hft (fun q => (hdW q t ht).2)
    let : SimplyConnectedSpace UnitTwoSphere := Poincare.Topology.standardSphereSimplyConnected 0
    let : LocallyPathConnectedSpace UnitTwoSphere :=
      ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) UnitTwoSphere
    have hcover := isLocalHomeomorph_iff_isCoveringMap.mp hlocal.isLocalHomeomorph
    have hbij := Poincare.Topology.bijective_of_isCoveringMap_of_simplyConnected hcover
    exact ⟨hlocal.diffeomorphOfBijective hbij, fun _ => rfl⟩
  let r := min d R / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hrd : 2 * r < d := by
    have hdR : 0 < min d R := lt_min hd hR
    have := min_le_left d R
    dsimp [r]
    linarith
  have hrR : 2 * r < R := by
    have hdR : 0 < min d R := lt_min hd hR
    have := min_le_right d R
    dsimp [r]
    linarith
  let b : ContDiffBump (0 : ℝ) := ⟨r, 2 * r, hr, by linarith⟩
  let σ : ℝ → ℝ := fun t => t * b t
  have hσ : ContDiff ℝ ∞ σ := contDiff_id.mul b.contDiff
  have hσnear (t : ℝ) (ht : |t| < r) : σ t = t := by
    have hb : b t = 1 := b.one_of_mem_closedBall
      (by simpa [Metric.mem_closedBall, Real.dist_eq] using ht.le)
    simp only [σ, hb, mul_one]
  have hσfar (t : ℝ) (ht : R ≤ |t|) : σ t = 0 := by
    have hb : b t = 0 := b.zero_of_le_dist
      (by simpa [Real.dist_eq] using hrR.le.trans ht)
    simp only [σ, hb, mul_zero]
  have hσbound (t : ℝ) : |σ t| < d := by
    by_cases ht : |t| < 2 * r
    · have hle : |t * b t| ≤ |t| := by
        rw [abs_mul, abs_of_nonneg b.nonneg]
        nlinarith [b.le_one (x := t), abs_nonneg t]
      exact hle.trans_lt (ht.trans hrd)
    · have hb : b t = 0 := b.zero_of_le_dist
        (by simpa [Real.dist_eq] using le_of_not_gt ht)
      simpa only [σ, hb, mul_zero, abs_zero] using hd
  choose E hE using fun t => hslice (σ t) (hσbound t)
  have hEsmooth : ContMDiff CylModel (𝓡 2) ∞
      (fun p : RoundCylinderSpace => E p.2 p.1) := by
    have heq : (fun p : RoundCylinderSpace => E p.2 p.1) =
        fun p => f (p.1, σ p.2) := funext fun p => hE p.2 p.1
    rw [heq]
    intro p
    exact (hf.contMDiffAt (hU.mem_nhds (hdW p.1 (σ p.2) (hσbound p.2)).1)).comp p
      (contMDiff_fst.prodMk (hσ.contMDiff.comp contMDiff_snd)).contMDiffAt
  obtain ⟨D, hD⟩ := exists_fiber_diffeomorph E hEsmooth
  refine ⟨r, D, hr, by linarith, ?_, ?_, ?_⟩
  · intro p
    rw [hD]
  · intro p hp
    refine ⟨(hdW p.1 p.2 (hp.trans (by linarith))).1, ?_⟩
    rw [hD, hE, hσnear p.2 hp]
  · intro p hp
    rw [hD, hE, hσfar p.2 hp, hzero]

theorem axial_deriv_comp_height_preserving
    (h : RoundCylinderSpace → ℝ)
    (D : Diffeomorph CylModel CylModel RoundCylinderSpace RoundCylinderSpace ∞)
    (hD : ∀ p : RoundCylinderSpace, (D p).2 = p.2)
    (hzero : ∀ q : UnitTwoSphere, h (q, 0) = 0) (q : UnitTwoSphere)
    (hh : ContMDiffAt CylModel 𝓘(ℝ, ℝ) ∞ h (D (q, 0))) :
    deriv (fun t : ℝ => h (D (q, t))) 0 =
      deriv (fun t : ℝ => h ((D (q, 0)).1, t)) 0 := by
  have hheight : (D (q, 0)).2 = 0 := hD (q, 0)
  have hpartial : (fun z : UnitTwoSphere => h (z, (D (q, 0)).2)) = fun _ => (0 : ℝ) := by
    funext z
    rw [hheight, hzero]
  have hfstzero : mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
      (fun z : UnitTwoSphere => h (z, (D (q, 0)).2)) (D (q, 0)).1 = 0 := by
    rw [hpartial, mfderiv_const]
  have hDsnd : (mfderiv CylModel CylModel D (q, 0) (0, 1)).2 = 1 := by
    have heq : (fun p : RoundCylinderSpace => (D p).2) = Prod.snd := funext hD
    have hc := mfderiv_comp (q, (0 : ℝ)) mdifferentiableAt_snd
      (D.contMDiff.mdifferentiableAt (by simp))
    change mfderiv CylModel 𝓘(ℝ, ℝ) (fun p => (D p).2) (q, 0) = _ at hc
    rw [heq, mfderiv_snd, mfderiv_snd] at hc
    have hv := congrArg (fun L => L (0, (1 : ℝ))) hc
    exact hv.symm
  have hcomp := mfderiv_comp (q, (0 : ℝ)) (hh.mdifferentiableAt (by simp))
    (D.contMDiff.mdifferentiableAt (by simp))
  have hv := congrArg (fun L => L (0, (1 : ℝ))) hcomp
  rw [mfderiv_prod_eq_add_apply
    ((hh.comp (q, (0 : ℝ)) D.contMDiff.contMDiffAt).mdifferentiableAt (by simp))] at hv
  simp only [map_zero, zero_add] at hv
  erw [mfderiv_eq_fderiv] at hv
  change (fderiv ℝ (fun t : ℝ => h (D (q, t))) 0) 1 =
    mfderiv CylModel 𝓘(ℝ, ℝ) h (D (q, 0))
      (mfderiv CylModel CylModel D (q, 0) (0, 1)) at hv
  rw [mfderiv_prod_eq_add_apply (hh.mdifferentiableAt (by simp)), hfstzero] at hv
  simp only [zero_apply, zero_add, hDsnd] at hv
  erw [mfderiv_eq_fderiv] at hv
  change (fderiv ℝ (fun t : ℝ => h (D (q, t))) 0) 1 =
    (fderiv ℝ (fun t : ℝ => h ((D (q, 0)).1, t)) (D (q, 0)).2) 1 at hv
  rw [fderiv_apply_one_eq_deriv, fderiv_apply_one_eq_deriv, hheight] at hv
  exact hv

theorem exists_supported_collar_germ_extension
    (F : RoundCylinderSpace → RoundCylinderSpace) (U : Set RoundCylinderSpace)
    (hU : IsOpen U) (hF : ContMDiffOn CylModel CylModel ∞ F U)
    (e : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞)
    (hUzero : ∀ q : UnitTwoSphere, (q, (0 : ℝ)) ∈ U)
    (hzero : ∀ q : UnitTwoSphere, F (q, 0) = (e q, 0))
    (hpos : ∀ q : UnitTwoSphere, 0 < deriv (fun t : ℝ => (F (q, t)).2) 0)
    (R : ℝ) (hR : 0 < R) :
    ∃ (r : ℝ) (E : Diffeomorph CylModel CylModel
        RoundCylinderSpace RoundCylinderSpace ∞),
      0 < r ∧ r < R ∧
      (∀ p : RoundCylinderSpace, |p.2| < r → p ∈ U ∧ E p = F p) ∧
      (∀ p : RoundCylinderSpace, R ≤ |p.2| → E p = (e p.1, p.2)) := by
  obtain ⟨s, D, hs, hsR, hDheight, hDlocal, hDout⟩ :=
    exists_supported_angular_germ_extension (fun p => (F p).1) U hU
      (contMDiff_fst.comp_contMDiffOn hF) e hUzero
      (fun q => congrArg Prod.fst (hzero q)) R hR
  have hDiheight (p : RoundCylinderSpace) : (D.symm p).2 = p.2 := by
    simpa only [D.apply_symm_apply] using (hDheight (D.symm p)).symm
  have hDzero (q : UnitTwoSphere) : D (q, 0) = (e q, 0) := by
    rw [(hDlocal (q, 0) (by simpa using hs)).2, hzero]
  have hDizero (q : UnitTwoSphere) : D.symm (q, 0) = (e.symm q, 0) := by
    apply D.injective
    change D (D.symm (q, 0)) = D (e.symm q, 0)
    rw [D.apply_symm_apply, hDzero, e.apply_symm_apply]
  have hDiU (q : UnitTwoSphere) (t : ℝ) (ht : |t| < s) : D.symm (q, t) ∈ U :=
    (hDlocal (D.symm (q, t)) (by simpa only [hDiheight] using ht)).1
  let c := s / 4
  have hc : 0 < c := by dsimp [c]; positivity
  have hcs : 2 * c < s := by dsimp [c]; linarith
  let b : ContDiffBump (0 : ℝ) := ⟨c, 2 * c, hc, by linarith⟩
  let σ : ℝ → ℝ := fun t => t * b t
  have hσ : ContDiff ℝ ∞ σ := contDiff_id.mul b.contDiff
  have hσnear (t : ℝ) (ht : |t| < c) : σ t = t := by
    have hb : b t = 1 := b.one_of_mem_closedBall
      (by simpa [Metric.mem_closedBall, Real.dist_eq] using ht.le)
    simp only [σ, hb, mul_one]
  have hσbound (t : ℝ) : |σ t| < s := by
    by_cases ht : |t| < 2 * c
    · have hle : |t * b t| ≤ |t| := by
        rw [abs_mul, abs_of_nonneg b.nonneg]
        nlinarith [b.le_one (x := t), abs_nonneg t]
      exact hle.trans_lt (ht.trans hcs)
    · have hb : b t = 0 := b.zero_of_le_dist
        (by simpa [Real.dist_eq] using le_of_not_gt ht)
      simpa only [σ, hb, mul_zero, abs_zero] using hs
  let h : RoundCylinderSpace → ℝ := fun p => (F (D.symm (p.1, σ p.2))).2
  have hh : ContMDiff CylModel 𝓘(ℝ, ℝ) ∞ h := by
    intro p
    exact contMDiffAt_snd.comp p
      ((hF.contMDiffAt (hU.mem_nhds (hDiU p.1 (σ p.2) (hσbound p.2)))).comp p
        (D.symm.contMDiff.comp
          (contMDiff_fst.prodMk (hσ.contMDiff.comp contMDiff_snd))).contMDiffAt)
  have hhzero (q : UnitTwoSphere) : h (q, 0) = 0 := by
    simp only [h, σ, zero_mul, hDizero, hzero]
  have hhpos (q : UnitTwoSphere) : 0 < deriv (fun t : ℝ => h (q, t)) 0 := by
    have heq : (fun t : ℝ => h (q, t)) =ᶠ[𝓝 0]
        (fun t : ℝ => (F (D.symm (q, t))).2) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hc] with t ht
      change (F (D.symm (q, σ t))).2 = (F (D.symm (q, t))).2
      rw [hσnear t (by simpa [Metric.mem_ball, Real.dist_eq] using ht)]
    rw [heq.deriv_eq]
    rw [axial_deriv_comp_height_preserving (fun p => (F p).2) D.symm hDiheight
      (fun q => congrArg Prod.snd (hzero q)) q
      (contMDiffAt_snd.comp _ (hF.contMDiffAt (hU.mem_nhds
        (hDiU q 0 (by simpa using hs)))))]
    exact hpos _
  obtain ⟨r, K, hr, hrR, hKfst, hKout, hKlocal⟩ :=
    exists_supported_scalar_collar_extension h hh hhzero hhpos R hR
  refine ⟨min r (min s c), D.trans K, lt_min hr (lt_min hs hc),
    (min_le_left _ _).trans_lt hrR, ?_, ?_⟩
  · intro p hp
    have hpr : |p.2| < r := hp.trans_le (min_le_left _ _)
    have hps : |p.2| < s := hp.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hpc : |p.2| < c := hp.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    refine ⟨(hDlocal p hps).1, ?_⟩
    change K (D p) = F p
    have hKD : K (D p) = ((D p).1, h (D p)) := by
      simpa only [Prod.eta] using hKlocal (D p).1 (D p).2
        (by simpa only [hDheight] using hpr)
    rw [hKD]
    apply Prod.ext
    · change (D p).1 = (F p).1
      simpa only using congrArg Prod.fst (hDlocal p hps).2
    · change (F (D.symm ((D p).1, σ (D p).2))).2 = (F p).2
      rw [hDheight, hσnear p.2 hpc]
      have hpair : ((D p).1, p.2) = D p := Prod.ext rfl (hDheight p).symm
      rw [hpair, D.symm_apply_apply]
  · intro p hp
    change K (D p) = (e p.1, p.2)
    rw [hKout (D p) (by simpa only [hDheight] using hp), hDout p hp]

theorem axial_deriv_ne_zero_of_zero_sphere_localDiffeomorph
    (F : RoundCylinderSpace → RoundCylinderSpace)
    (hzero : ∀ q : UnitTwoSphere, (F (q, 0)).2 = 0) (q : UnitTwoSphere)
    (hF : IsLocalDiffeomorphAt CylModel CylModel ∞ F (q, 0)) :
    deriv (fun t : ℝ => (F (q, t)).2) 0 ≠ 0 := by
  intro hd0
  let h : RoundCylinderSpace → ℝ := fun p => (F p).2
  have hh : ContMDiffAt CylModel 𝓘(ℝ, ℝ) ∞ h (q, 0) :=
    contMDiffAt_snd.comp _ hF.contMDiffAt
  have hpartial : (fun z : UnitTwoSphere => h (z, 0)) = fun _ => (0 : ℝ) :=
    funext hzero
  have hderiv (v : EuclideanSpace ℝ (Fin 2) × ℝ) :
      mfderiv CylModel 𝓘(ℝ, ℝ) h (q, 0) v = 0 := by
    rw [mfderiv_prod_eq_add_apply (hh.mdifferentiableAt (by simp)), hpartial,
      mfderiv_const, zero_apply, zero_add]
    erw [mfderiv_eq_fderiv]
    change fderiv ℝ (fun t : ℝ => (F (q, t)).2) 0 v.2 = (0 : ℝ)
    rw [fderiv_eq_deriv_mul]
    rw [hd0, zero_mul]
  obtain ⟨v, hv⟩ := (hF.mfderivToContinuousLinearEquiv (by simp)).surjective (0, (1 : ℝ))
  change mfderiv CylModel CylModel F (q, 0) v = (0, 1) at hv
  have hc := mfderiv_comp (q, (0 : ℝ)) mdifferentiableAt_snd (hF.mdifferentiableAt (by simp))
  have hc' : (mfderiv CylModel 𝓘(ℝ, ℝ) h (q, 0) v : ℝ) = 1 := by
    change (mfderiv CylModel 𝓘(ℝ, ℝ) (Prod.snd ∘ F) (q, 0) v : ℝ) = 1
    rw [hc, mfderiv_snd]
    change (mfderiv CylModel CylModel F (q, 0) v).2 = 1
    rw [hv]
  rw [hderiv] at hc'
  exact (zero_ne_one : (0 : ℝ) ≠ 1) hc'

theorem axial_deriv_pos_of_zero_sphere_localDiffeomorph
    (F : RoundCylinderSpace → RoundCylinderSpace)
    (hzero : ∀ q : UnitTwoSphere, (F (q, 0)).2 = 0) (q : UnitTwoSphere)
    (hF : IsLocalDiffeomorphAt CylModel CylModel ∞ F (q, 0))
    {r : ℝ} (hr : 0 < r)
    (hpositive : ∀ t : ℝ, 0 < t → t < r → 0 < (F (q, t)).2) :
    0 < deriv (fun t : ℝ => (F (q, t)).2) 0 := by
  have hd : DifferentiableAt ℝ (fun t : ℝ => (F (q, t)).2) 0 :=
    ((contMDiffAt_snd.comp _ hF.contMDiffAt).comp 0
      (contMDiff_const.prodMk contMDiff_id).contMDiffAt).contDiffAt.differentiableAt (by simp)
  have hn : 0 ≤ deriv (fun t : ℝ => (F (q, t)).2) 0 := by
    apply ge_of_tendsto hd.hasDerivAt.tendsto_slope_zero_right
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hr)] with t ht htr
    have ht0 : 0 < t := ht
    simpa only [zero_add, hzero, sub_zero, smul_eq_mul] using
      mul_nonneg (inv_nonneg.mpr ht0.le) (hpositive t ht0 htr).le
  exact lt_of_le_of_ne hn (axial_deriv_ne_zero_of_zero_sphere_localDiffeomorph F hzero q hF).symm

end PoincareConjecture.CylinderGluing
