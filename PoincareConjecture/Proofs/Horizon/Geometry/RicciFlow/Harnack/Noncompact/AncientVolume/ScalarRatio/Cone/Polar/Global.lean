import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Polar.Tensor
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Positive.Metric








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000

open Set Filter TopologicalSpace PoincareConjecture Manifold IsManifold
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology NNReal ENNReal Bundle

namespace Poincare.AncientVolume.ScalarRatio

variable {X : Type*} [MetricSpace X] {p : X} (hc : RayComparison p)


def positiveConeRadii : Opens ℝ := ⟨Ioi 0, isOpen_Ioi⟩


def positiveConePolarMap (q : positiveConeRadii × AsymptoticConeUnitSlice p hc) :
    AsymptoticConePositive p hc :=
  ⟨asymptoticConeDilation hc ⟨q.1.1, q.1.2.le⟩ q.2.1, by
    rw [asymptoticConeRadius_dilation, q.2.property, mul_one]
    exact q.1.2⟩


def positiveConePolarInverse (a : AsymptoticConePositive p hc) :
    positiveConeRadii × AsymptoticConeUnitSlice p hc :=
  (⟨(asymptoticConeRadius hc a.1 : ℝ), a.property⟩, asymptoticConeNormalize hc a)

theorem positiveConePolarInverse_left (q : positiveConeRadii × AsymptoticConeUnitSlice p hc) :
    positiveConePolarInverse hc (positiveConePolarMap hc q) = q := by
  apply Prod.ext
  · apply Subtype.ext
    change ((asymptoticConeRadius hc (asymptoticConeDilation hc ⟨q.1.1, q.1.2.le⟩ q.2.1)) : ℝ) = q.1.1
    rw [asymptoticConeRadius_dilation, q.2.property, mul_one]
    rfl
  · apply Subtype.ext
    change asymptoticConeDilation hc
      (asymptoticConeRadius hc (asymptoticConeDilation hc ⟨q.1.1, q.1.2.le⟩ q.2.1))⁻¹
      (asymptoticConeDilation hc ⟨q.1.1, q.1.2.le⟩ q.2.1) = q.2.1
    rw [asymptoticConeRadius_dilation, q.2.property, mul_one, asymptoticConeDilation_mul,
      inv_mul_cancel₀ (show (⟨q.1.1, q.1.2.le⟩ : ℝ≥0) ≠ 0 from (show 0 < (⟨q.1.1, q.1.2.le⟩ : ℝ≥0) from q.1.2).ne'),
      asymptoticConeDilation_one]

theorem positiveConePolarInverse_right (a : AsymptoticConePositive p hc) :
    positiveConePolarMap hc (positiveConePolarInverse hc a) = a := by
  apply Subtype.ext
  change asymptoticConeDilation hc (asymptoticConeRadius hc a.1)
    (asymptoticConeDilation hc (asymptoticConeRadius hc a.1)⁻¹ a.1) = a.1
  rw [asymptoticConeDilation_mul, mul_inv_cancel₀ a.property.ne', asymptoticConeDilation_one]

def positiveConePolarEquiv :
    (positiveConeRadii × AsymptoticConeUnitSlice p hc) ≃ AsymptoticConePositive p hc where
  toFun := positiveConePolarMap hc
  invFun := positiveConePolarInverse hc
  left_inv := positiveConePolarInverse_left hc
  right_inv := positiveConePolarInverse_right hc

variable {hc} {n : ℕ}
  (hne : Nonempty (AsymptoticConePositive p hc))
  (hcover : ∀ z : AsymptoticConeUnitSlice p hc,
    ∃ (d : UnitSliceRadialChartData hc n) (x : d.Level), (d.levelHomeomorph x).1 = z)

private theorem polar_chart_coneImage (d : UnitSliceRadialChartData hc n)
    (c : ℝ≥0) (_hcpos : 0 < c)
    (Q : OpenPartialHomeomorph (ℝ × d.Level) (UnitSliceAmbient n))
    (hradius : ∀ y ∈ Q.target, (Q.symm y).1 = (c : ℝ) *
      (asymptoticConeRadius hc (d.ambientChart y) : ℝ))
    (hangle : ∀ y ∈ Q.target,
      d.ambientChart (openLevelIncl d.potential d.source (1 / 2) (Q.symm y).2) =
        asymptoticConeDilation hc (asymptoticConeRadius hc (d.ambientChart y))⁻¹ (d.ambientChart y))
    (q : ℝ × d.Level) (hq : q ∈ Q.source) (hpos : 0 < q.1) :
    asymptoticConeDilation hc c (d.ambientChart (Q q)) =
      asymptoticConeDilation hc ⟨q.1, hpos.le⟩
        (d.ambientChart (openLevelIncl d.potential d.source (1 / 2) q.2)) := by
  have hr := hradius (Q q) (Q.map_source hq)
  have ha := hangle (Q q) (Q.map_source hq)
  rw [Q.left_inv hq] at hr ha
  have hscale : (⟨q.1, hpos.le⟩ : ℝ≥0) = c * asymptoticConeRadius hc (d.ambientChart (Q q)) :=
    Subtype.ext hr
  have hnonzero : asymptoticConeRadius hc (d.ambientChart (Q q)) ≠ 0 := by
    intro hz
    simp only [hz, NNReal.coe_zero, mul_zero] at hr
    linarith
  rw [ha, asymptoticConeDilation_mul, hscale, mul_assoc, mul_inv_cancel₀ hnonzero, mul_one]



theorem isLocalDiffeomorph_positiveConePolarMap :
    letI := unitSliceChartedSpace hc n hcover
    letI := unitSlice_isManifold hc n hcover
    letI := positiveConeChartedSpace hc n hne hcover
    letI := positiveCone_isManifold hc n hne hcover
    IsLocalDiffeomorph (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 (n + 1)) ∞ (positiveConePolarMap hc) := by
  let := unitSliceChartedSpace hc n hcover
  let := unitSlice_isManifold hc n hcover
  let := positiveConeChartedSpace hc n hne hcover
  let := positiveCone_isManifold hc n hne hcover
  rintro ⟨r, u⟩
  obtain ⟨d, z, hz⟩ := hcover u
  subst u
  let c : ℝ≥0 := ⟨r.1, r.2.le⟩
  have hcpos : 0 < c := r.2
  obtain ⟨Q, hzQ, hQz, hQtarget, hQ, hQsmooth, hQinverse, hradius, hangle, _⟩ :=
    d.exists_smooth_polar_coordinates c hcpos z
  let P : PartialDiffeomorph (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 (n + 1))
      (ℝ × d.Level) (UnitSliceAmbient n) ∞ := {
    toPartialEquiv := Q.toPartialEquiv
    open_source := Q.open_source
    open_target := Q.open_target
    contMDiffOn_toFun := hQsmooth
    contMDiffOn_invFun := hQinverse }
  obtain ⟨A, hrA, hA⟩ := Poincare.isLocalDiffeomorph_opensSubtypeVal 𝓘(ℝ, ℝ) positiveConeRadii r
  have hl := d.isLocalDiffeomorph_levelMap hc n hcover z
  let B := hl.localInverse
  let K : PartialDiffeomorph (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓘(ℝ, ℝ).prod (𝓡 n))
      (positiveConeRadii × AsymptoticConeUnitSlice p hc) (ℝ × d.Level) ∞ := {
    toPartialEquiv := A.toPartialEquiv.prod B.toPartialEquiv
    open_source := A.open_source.prod B.open_source
    open_target := A.open_target.prod B.open_target
    contMDiffOn_toFun := A.contMDiffOn.prodMap B.contMDiffOn
    contMDiffOn_invFun := A.symm.contMDiffOn.prodMap B.symm.contMDiffOn }
  let e := (d.dilate c hcpos).positiveChart hne
  have he : e ∈ maximalAtlas (𝓡 (n + 1)) ∞ (AsymptoticConePositive p hc) :=
    subset_maximalAtlas ⟨d.dilate c hcpos, rfl⟩
  let C : PartialDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1))
      (AsymptoticConePositive p hc) (UnitSliceAmbient n) ∞ := {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas he
    contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas he }
  let R := K.trans (P.trans C.symm)
  have hK : K (r, (d.levelHomeomorph z).1) = ((c : ℝ), z) := by
    apply Prod.ext
    · exact (hA hrA).symm
    · exact hl.localInverse_left_inv hl.localInverse_mem_target
  have hsource : (r, (d.levelHomeomorph z).1) ∈ R.source := by
    refine ⟨⟨hrA, hl.localInverse_mem_source⟩, ?_⟩
    change K (r, (d.levelHomeomorph z).1) ∈ (P.trans C.symm).source
    rw [hK]
    refine ⟨hzQ, ?_⟩
    change Q ((c : ℝ), z) ∈ e.target
    rw [hQz, UnitSliceRadialChartData.positiveChart_target]
    exact z.1.2
  refine ⟨R, hsource, ?_⟩
  intro a ha
  have haK : a ∈ K.source := ha.1
  have haQ : K a ∈ Q.source := ha.2.1
  have haC : Q (K a) ∈ e.target := ha.2.2
  have hKfirst : (K a).1 = a.1.1 := (hA haK.1).symm
  have hKsecond : (d.levelHomeomorph (K a).2).1 = a.2 := hl.localInverse_right_inv haK.2
  apply Subtype.ext
  change asymptoticConeDilation hc ⟨a.1.1, a.1.2.le⟩ a.2.1 = (e.symm (Q (K a))).1
  rw [UnitSliceRadialChartData.positiveChart_symm_val _ hne haC,
    UnitSliceRadialChartData.dilate_apply]
  rw [polar_chart_coneImage d c hcpos Q hradius hangle (K a) haQ (hQ (K a) haQ).1]
  have hsecond : d.ambientChart (openLevelIncl d.potential d.source (1 / 2) (K a).2) = a.2.1 :=
    congrArg Subtype.val hKsecond
  rw [hsecond]
  congr 1
  exact Subtype.ext hKfirst.symm



def positiveConePolarDiffeomorph :
    letI := unitSliceChartedSpace hc n hcover
    letI := unitSlice_isManifold hc n hcover
    letI := positiveConeChartedSpace hc n hne hcover
    letI := positiveCone_isManifold hc n hne hcover
    (positiveConeRadii × AsymptoticConeUnitSlice p hc) ≃ₘ⟮𝓘(ℝ, ℝ).prod (𝓡 n), 𝓡 (n + 1)⟯
      AsymptoticConePositive p hc := by
  let := unitSliceChartedSpace hc n hcover
  let := unitSlice_isManifold hc n hcover
  let := positiveConeChartedSpace hc n hne hcover
  let := positiveCone_isManifold hc n hne hcover
  exact (isLocalDiffeomorph_positiveConePolarMap hne hcover).diffeomorphOfBijective
    (positiveConePolarEquiv hc).bijective

theorem positiveConePolarDiffeomorph_apply :
    letI := unitSliceChartedSpace hc n hcover
    letI := unitSlice_isManifold hc n hcover
    letI := positiveConeChartedSpace hc n hne hcover
    letI := positiveCone_isManifold hc n hne hcover
    ∀ q, positiveConePolarDiffeomorph hne hcover q = positiveConePolarMap hc q := by
  intros
  rfl

theorem positiveConePolarDiffeomorph_symm_apply :
    letI := unitSliceChartedSpace hc n hcover
    letI := unitSlice_isManifold hc n hcover
    letI := positiveConeChartedSpace hc n hne hcover
    letI := positiveCone_isManifold hc n hne hcover
    ∀ a, (positiveConePolarDiffeomorph hne hcover).symm a = positiveConePolarInverse hc a := by
  let := unitSliceChartedSpace hc n hcover
  let := unitSlice_isManifold hc n hcover
  let := positiveConeChartedSpace hc n hne hcover
  let := positiveCone_isManifold hc n hne hcover
  intro a
  apply (positiveConePolarEquiv hc).injective
  change positiveConePolarMap hc _ = positiveConePolarMap hc _
  rw [positiveConePolarInverse_right]
  exact (positiveConePolarDiffeomorph hne hcover).apply_symm_apply a

private theorem positiveConeMetric_chart_symm_inner (d : UnitSliceRadialChartData hc n) :
    letI := positiveConeChartedSpace hc n hne hcover
    letI := positiveCone_isManifold hc n hne hcover
    ∀ x ∈ d.ambientChart.source, ∀ v w : UnitSliceAmbient n,
      (positiveConeMetric hne hcover).inner ((d.positiveChart hne).symm x)
        (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) (d.positiveChart hne).symm x v)
        (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) (d.positiveChart hne).symm x w) = d.metric.inner x v w := by
  let := positiveConeChartedSpace hc n hne hcover
  let := positiveCone_isManifold hc n hne hcover
  intro x hx v w
  let y : d.source := ⟨x, hx⟩
  let C := d.positiveChart hne
  have hmax : C ∈ maximalAtlas (𝓡 (n + 1)) ∞ (AsymptoticConePositive p hc) :=
    subset_maximalAtlas ⟨d, rfl⟩
  have hdiff : MDifferentiableAt (𝓡 (n + 1)) (𝓡 (n + 1)) C.symm x :=
    ((contMDiffOn_symm_of_mem_maximalAtlas hmax).contMDiffAt
      (C.open_target.mem_nhds (by rw [d.positiveChart_target]; exact hx))).mdifferentiableAt (by simp)
  have hfun : d.positiveMap = fun z : d.source => C.symm z :=
    funext (d.positiveMap_eq_chart_symm hne)
  have hderiv (u : UnitSliceAmbient n) :
      mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) d.positiveMap y u =
        mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) C.symm x u := by
    rw [hfun]
    exact congrArg (fun L => L u) (mfderiv_opens_restrict d.source C.symm (x := y) hdiff)
  have hm := positiveConeMetric_inner hne hcover d y v w
  rw [hderiv v, hderiv w, d.positiveMap_eq_chart_symm hne] at hm
  exact hm.symm

private theorem positiveConePolarMap_inner_level
    (d : UnitSliceRadialChartData hc n) (r : positiveConeRadii) (z : d.Level) :
    letI := unitSliceChartedSpace hc n hcover
    letI := unitSlice_isManifold hc n hcover
    letI := positiveConeChartedSpace hc n hne hcover
    letI := positiveCone_isManifold hc n hne hcover
    ∀ a b : ℝ, ∀ v w : EuclideanSpace ℝ (Fin n),
      let l := fun z : d.Level => (d.levelHomeomorph z).1
      (positiveConeMetric hne hcover).inner (positiveConePolarMap hc (r, l z))
        (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 (n + 1)) (positiveConePolarMap hc) (r, l z)
          (a, mfderiv (𝓡 n) (𝓡 n) l z v))
        (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 (n + 1)) (positiveConePolarMap hc) (r, l z)
          (b, mfderiv (𝓡 n) (𝓡 n) l z w)) =
            a * b + r.1 ^ 2 * d.levelMetric.inner z v w := by
  let := unitSliceChartedSpace hc n hcover
  let := unitSlice_isManifold hc n hcover
  let := positiveConeChartedSpace hc n hne hcover
  let := positiveCone_isManifold hc n hne hcover
  intro a b v w
  let I := 𝓘(ℝ, ℝ).prod (𝓡 n)
  let l := fun z : d.Level => (d.levelHomeomorph z).1
  let c : ℝ≥0 := ⟨r.1, r.2.le⟩
  have hcpos : 0 < c := r.2
  obtain ⟨Q, hzQ, hQz, hQtarget, hQ, hQsmooth, _, hradius, hangle, hQtensor⟩ :=
    d.exists_smooth_polar_coordinates c hcpos z
  let e := (d.dilate c hcpos).positiveChart hne
  have he : e ∈ maximalAtlas (𝓡 (n + 1)) ∞ (AsymptoticConePositive p hc) :=
    subset_maximalAtlas ⟨d.dilate c hcpos, rfl⟩
  let i : positiveConeRadii × d.Level → ℝ × d.Level := Prod.map Subtype.val id
  let j : positiveConeRadii × d.Level → positiveConeRadii × AsymptoticConeUnitSlice p hc := Prod.map id l
  have hi : ContMDiff I I ∞ i := contMDiff_subtype_val.prodMap contMDiff_id
  have hl := d.isLocalDiffeomorph_levelMap hc n hcover
  have hj : ContMDiff I I ∞ j := contMDiff_id.prodMap hl.contMDiff
  have hEq : positiveConePolarMap hc ∘ j =ᶠ[𝓝 (r, z)] e.symm ∘ Q ∘ i := by
    have hnear := (hi (r, z)).continuousAt.preimage_mem_nhds (Q.open_source.mem_nhds hzQ)
    filter_upwards [hnear] with u hu
    apply Subtype.ext
    change asymptoticConeDilation hc ⟨u.1.1, u.1.2.le⟩ (l u.2).1 = (e.symm (Q (i u))).1
    rw [UnitSliceRadialChartData.positiveChart_symm_val _ hne
      (by rw [UnitSliceRadialChartData.positiveChart_target]; exact hQtarget (Q.map_source hu)),
      UnitSliceRadialChartData.dilate_apply,
      polar_chart_coneImage d c hcpos Q hradius hangle (i u) hu (hQ (i u) hu).1]
    rfl
  have hQdiff := (hQsmooth.contMDiffAt (Q.open_source.mem_nhds hzQ)).mdifferentiableAt (by simp)
  have hediff : MDifferentiableAt (𝓡 (n + 1)) (𝓡 (n + 1)) e.symm (Q (i (r, z))) :=
    ((contMDiffOn_symm_of_mem_maximalAtlas he).contMDiffAt (e.open_target.mem_nhds
      (by rw [UnitSliceRadialChartData.positiveChart_target]; exact hQtarget (Q.map_source hzQ)))).mdifferentiableAt (by simp)
  have hleft := mfderiv_comp (r, z)
    ((isLocalDiffeomorph_positiveConePolarMap hne hcover).mdifferentiable (by simp) (j (r, z)))
    ((hj (r, z)).mdifferentiableAt (by simp))
  have hright := mfderiv_comp (r, z) hediff
    (hQdiff.comp (r, z) ((hi (r, z)).mdifferentiableAt (by simp)))
  erw [mfderiv_comp (r, z) hQdiff ((hi (r, z)).mdifferentiableAt (by simp))] at hright
  have hderiv (a : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
      mfderiv I (𝓡 (n + 1)) (positiveConePolarMap hc) (r, l z)
        (a, mfderiv (𝓡 n) (𝓡 n) l z v) =
      mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) e.symm (Q ((c : ℝ), z))
        (mfderiv I (𝓡 (n + 1)) Q ((c : ℝ), z) (a, v)) := by
    have hd := congrArg (fun L => L (a, v)) (hEq.mfderiv_eq (I := I) (I' := 𝓡 (n + 1)))
    erw [hleft, hright] at hd
    have hDj : mfderiv I I j (r, z) (a, v) = (a, mfderiv (𝓡 n) (𝓡 n) l z v) := by
      rw [mfderiv_prodMap mdifferentiableAt_id (hl.mdifferentiable (by simp) z), mfderiv_id]
      rfl
    have hDi : mfderiv I I i (r, z) (a, v) = (a, v) := by
      rw [mfderiv_prodMap
        ((Poincare.isLocalDiffeomorph_opensSubtypeVal 𝓘(ℝ, ℝ) positiveConeRadii).mdifferentiable (by simp) r)
        mdifferentiableAt_id, mfderiv_id]
      change (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (Subtype.val : positiveConeRadii → ℝ) r a, v) = (a, v)
      rw [mfderiv_opens_subtypeVal_apply]
    change mfderiv I (𝓡 (n + 1)) (positiveConePolarMap hc) (j (r, z))
      (mfderiv I I j (r, z) (a, v)) =
      mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) e.symm (Q (i (r, z)))
        (mfderiv I (𝓡 (n + 1)) Q (i (r, z)) (mfderiv I I i (r, z) (a, v))) at hd
    erw [hDj, hDi] at hd
    exact hd
  have hvalue := hEq.eq_of_nhds
  change positiveConePolarMap hc (r, l z) = e.symm (Q ((c : ℝ), z)) at hvalue
  change (positiveConeMetric hne hcover).inner (positiveConePolarMap hc (r, l z)) _ _ = _
  erw [hderiv a v, hderiv b w, hvalue]
  have hmetric := positiveConeMetric_chart_symm_inner hne hcover (d.dilate c hcpos)
    (Q ((c : ℝ), z)) (hQtarget (Q.map_source hzQ))
    (mfderiv I (𝓡 (n + 1)) Q ((c : ℝ), z) (a, v))
    (mfderiv I (𝓡 (n + 1)) Q ((c : ℝ), z) (b, w))
  exact hmetric.trans (hQtensor ((c : ℝ), z) hzQ a b v w)



theorem positiveConePolarMap_inner :
    letI := unitSliceChartedSpace hc n hcover
    letI := unitSlice_isManifold hc n hcover
    letI := positiveConeChartedSpace hc n hne hcover
    letI := positiveCone_isManifold hc n hne hcover
    ∀ q : positiveConeRadii × AsymptoticConeUnitSlice p hc,
      ∀ a b : ℝ, ∀ v w : EuclideanSpace ℝ (Fin n),
      (positiveConeMetric hne hcover).inner (positiveConePolarMap hc q)
        (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 (n + 1)) (positiveConePolarMap hc) q (a, v))
        (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 (n + 1)) (positiveConePolarMap hc) q (b, w)) =
          a * b + q.1.1 ^ 2 * (unitSliceMetric hcover).inner q.2 v w := by
  let := unitSliceChartedSpace hc n hcover
  let := unitSlice_isManifold hc n hcover
  let := positiveConeChartedSpace hc n hne hcover
  let := positiveCone_isManifold hc n hne hcover
  rintro ⟨r, u⟩ a b v w
  obtain ⟨d, z, hz⟩ := hcover u
  subst u
  have hl := d.isLocalDiffeomorph_levelMap hc n hcover z
  obtain ⟨v', hv⟩ := (hl.mfderivToContinuousLinearEquiv (by simp)).surjective v
  obtain ⟨w', hw⟩ := (hl.mfderivToContinuousLinearEquiv (by simp)).surjective w
  change mfderiv (𝓡 n) (𝓡 n) (fun z : d.Level => (d.levelHomeomorph z).1) z v' = v at hv
  change mfderiv (𝓡 n) (𝓡 n) (fun z : d.Level => (d.levelHomeomorph z).1) z w' = w at hw
  have hm := positiveConePolarMap_inner_level hne hcover d r z a b v' w'
  dsimp only at hm
  have hlink := unitSliceMetric_inner hcover d z v' w'
  rw [hv, hw] at hlink
  rw [hv, hw, hlink] at hm
  exact hm

end Poincare.AncientVolume.ScalarRatio
