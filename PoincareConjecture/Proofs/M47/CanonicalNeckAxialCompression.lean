import PoincareConjecture.Proofs.M47.CanonicalNeckAxialError

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff BigOperators Topology

namespace PoincareConjecture.Proofs.M47

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "V" => RoundCylinderCoordinates

theorem neckAxialCoordinate_mem_open_interval
    {epsilon lambda c z : ℝ} (_hepsilon : 0 < epsilon)
    (hlambda : lambda ∈ Ioo (0 : ℝ) 1)
    (hc : |c| < (1 - lambda) * epsilon⁻¹)
    (hz : z ∈ Icc (-epsilon⁻¹) epsilon⁻¹) :
    lambda * z + c ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ := by
  have hzabs : |z| ≤ epsilon⁻¹ := abs_le.mpr hz
  have hlt : |lambda * z + c| < epsilon⁻¹ := by
    calc
      _ ≤ |lambda * z| + |c| := abs_add_le _ _
      _ = lambda * |z| + |c| := by rw [abs_mul, abs_of_pos hlambda.1]
      _ ≤ lambda * epsilon⁻¹ + |c| :=
        add_le_add (mul_le_mul_of_nonneg_left hzabs hlambda.1.le) le_rfl
      _ < lambda * epsilon⁻¹ + (1 - lambda) * epsilon⁻¹ :=
        add_lt_add_of_le_of_lt le_rfl hc
      _ = epsilon⁻¹ := by ring
  exact abs_lt.mp hlt

theorem roundCylinderTensorSmoothOn_neckAxialTensorPullback
    {epsilon lambda c : ℝ} (hepsilon : 0 < epsilon)
    (hlambda : lambda ∈ Ioo (0 : ℝ) 1)
    (hc : |c| < (1 - lambda) * epsilon⁻¹)
    (B : RoundCylinderSpace → V →L[ℝ] V →L[ℝ] ℝ)
    (hB : RoundCylinderTensorSmoothOn epsilon (fun z v w => B z v w)) :
    RoundCylinderTensorSmoothOn epsilon
      (neckAxialTensorPullback lambda c (fun z v w => B z v w)) := by
  intro q a b
  have hA : ContDiff ℝ ∞ (neckAxialCoordinate lambda c) :=
    contDiff_fst.prodMk ((contDiff_const.mul contDiff_snd).add contDiff_const)
  have hmaps : MapsTo (neckAxialCoordinate lambda c)
      ((chartAt E₂ q).target ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹)
      ((chartAt E₂ q).target ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹) := by
    intro p hp
    exact ⟨hp.1, neckAxialCoordinate_mem_open_interval hepsilon hlambda hc
      ⟨hp.2.1.le, hp.2.2.le⟩⟩
  have hcomp := (hB q a b).comp hA.contDiffOn hmaps
  have hprod : ContDiffOn ℝ ∞ (fun p : V =>
      neckAxialWeight lambda a * neckAxialWeight lambda b *
        roundCylinderTensorCoefficient (fun z v w => B z v w) (chartAt E₂ q)
          (neckAxialCoordinate lambda c p) a b)
      ((chartAt E₂ q).target ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹) :=
    contDiffOn_const.mul hcomp
  exact hprod.congr fun p _ =>
    roundCylinderTensorCoefficient_neckAxialTensorPullback lambda c B q p a b

theorem exists_same_epsilon_neck_axial_compression
    {epsilon : ℝ} (hepsilon : 0 < epsilon) {I : Set ℝ}
    (hI : ∀ u ∈ I, u ≤ 0)
    (B : ℝ → RoundCylinderSpace → V →L[ℝ] V →L[ℝ] ℝ)
    (hB : RoundCylinderFamilyClose epsilon I (fun u z v w => B u z v w)) :
    ∃ lambda : ℝ, lambda ∈ Ioo (0 : ℝ) 1 ∧
      ∀ c : ℝ, |c| < (1 - lambda) * epsilon⁻¹ →
        RoundCylinderFamilyClose epsilon I
          (fun u => neckAxialTensorPullback lambda c (fun z v w => B u z v w)) := by
  obtain ⟨hsmooth, b, hb, hbound⟩ := hB
  let theta := (epsilon ^ 2 - b) / (2 * (|b| + 1))
  have htheta : 0 < theta := div_pos (sub_pos.mpr hb) (by positivity)
  have hthetab : theta * (|b| + 1) = (epsilon ^ 2 - b) / 2 := by
    dsimp only [theta]
    field_simp
  have hscaled : theta * b ≤ (epsilon ^ 2 - b) / 2 := by
    calc
      _ ≤ theta * |b| := mul_le_mul_of_nonneg_left (le_abs_self b) htheta.le
      _ ≤ theta * (|b| + 1) := mul_le_mul_of_nonneg_left (by linarith) htheta.le
      _ = _ := hthetab
  have hbase : (1 + theta) * b < epsilon ^ 2 := by nlinarith
  let E (lambda : ℝ) :=
    (1 + theta) * b + (1 + theta⁻¹) * (lambda ^ 2 - 1) ^ 2
  have hE : Continuous E := by
    exact continuous_const.add (continuous_const.mul
      (((continuous_id.pow 2).sub continuous_const).pow 2))
  have hnear : ∀ᶠ lambda : ℝ in 𝓝 1, E lambda < epsilon ^ 2 :=
    hE.continuousAt.eventually_lt continuousAt_const (by
      simpa only [E, one_pow, sub_self, zero_pow (by decide : 2 ≠ 0),
        mul_zero, add_zero] using hbase)
  have hleft : ∀ᶠ lambda : ℝ in 𝓝[<] 1,
      lambda ∈ Ioo (0 : ℝ) 1 ∧ E lambda < epsilon ^ 2 := by
    have hpositive : ∀ᶠ lambda : ℝ in 𝓝 1, 0 < lambda := Ioi_mem_nhds zero_lt_one
    filter_upwards [self_mem_nhdsWithin,
      hpositive.filter_mono nhdsWithin_le_nhds,
      hnear.filter_mono nhdsWithin_le_nhds] with lambda h1 h0 h
    exact ⟨⟨h0, h1⟩, h⟩
  obtain ⟨lambda, hlambda, hsmall⟩ := hleft.exists
  refine ⟨lambda, hlambda, ?_⟩
  intro c hc
  refine ⟨fun u hu => roundCylinderTensorSmoothOn_neckAxialTensorPullback
    hepsilon hlambda hc (B u) (hsmooth u hu), E lambda, hsmall, ?_⟩
  intro u hu z hz
  have himage := neckAxialCoordinate_mem_open_interval hepsilon hlambda hc
    ⟨hz.1.le, hz.2.le⟩
  apply (roundCylinderJetErrorSquared_neckAxialTensorPullback_le
    ⟨hlambda.1.le, hlambda.2.le⟩ (hI u hu) htheta c (B u) (hsmooth u hu)
    (Nat.floor epsilon⁻¹) z himage).trans
  exact add_le_add
    (mul_le_mul_of_nonneg_left (hbound u hu (neckAxialSpaceMap lambda c z) himage)
      (show 0 ≤ 1 + theta by positivity)) le_rfl

theorem isCompact_neckAxialSpaceMap_closed_cylinder
    {epsilon lambda c : ℝ} (hepsilon : 0 < epsilon)
    (hlambda : lambda ∈ Ioo (0 : ℝ) 1)
    (hc : |c| < (1 - lambda) * epsilon⁻¹) :
    IsCompact (neckAxialSpaceMap lambda c ''
      (univ ×ˢ Icc (-epsilon⁻¹) epsilon⁻¹)) ∧
    neckAxialSpaceMap lambda c '' (univ ×ˢ Icc (-epsilon⁻¹) epsilon⁻¹) ⊆
      univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹ := by
  refine ⟨(isCompact_univ.prod isCompact_Icc).image
    (neckAxialSpaceMap_contMDiff lambda c).continuous, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨mem_univ _, neckAxialCoordinate_mem_open_interval hepsilon hlambda hc hz.2⟩

end PoincareConjecture.Proofs.M47
