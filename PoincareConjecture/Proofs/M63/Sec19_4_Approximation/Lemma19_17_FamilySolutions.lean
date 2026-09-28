import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.CanonicalRampInitialFamilyBounds
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.WholeFamilyThreeJetContinuity
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.PeriodicC1LoopFamily
import PoincareConjecture.Proofs.M63.Sec19_3_Ramps.Lemma19_14_ExistenceFromLocal
import PoincareConjecture.Proofs.M63.Sec19_3_Ramps.Cor19_13_DegreePreservation
import PoincareConjecture.Proofs.M63.Sec19_2_CurveEstimates.C2EstimatesFromLocal
import PoincareConjecture.Proofs.M59.Sec18_3_LoopSpace.NullLoopHomotopy
import PoincareConjecture.Proofs.M58.Cor18_28_PeriodicSpeed

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff Topology unitInterval

universe u

namespace PoincareConjecture

open M63 Proofs.M58

theorem m63ProductSolutionFamily_nonempty
    {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    {a b : ℝ} (F : RicciFlow 3 M (Icc a b))
    (hcompact : IsCompact (univ : Set M)) (hM62 : M62CurveEvolutionTheory.{u})
    (G : M63AmbientGeometry F)
    {Gamma : C(LoopTwoSphere, C1FreeLoopSpace (M := M))} {zeta : ℝ}
    (A : M63RawApproximation F Gamma zeta)
    (circumference : ℝ) (hcirc : 0 < circumference) :
    Nonempty (M63ProductSolutionFamily (G.product circumference hcirc) A) := by
  classical
  let P := G.product circumference hcirc
  let : CompactSpace M := isCompact_univ_iff.mp hcompact
  let : Fact (0 < circumference) := ⟨hcirc⟩
  let z0 : LoopTwoSphere := ⟨EuclideanSpace.single (0 : Fin 3) 1, by simp⟩
  let : Nonempty M := ⟨periodicFreeLoop (A.family z0) 0⟩
  let sphereHomeo : Metric.sphere (0 : LoopAmbient) 1 ≃ₜ LoopTwoSphere :=
    Homeomorph.setCongr (by ext z; exact mem_sphere_zero_iff_norm)
  let : CompactSpace LoopTwoSphere := sphereHomeo.compactSpace
  have hcompactP : IsCompact (univ : Set P.charts.Point) := isCompact_univ
  have hab : a < b := by
    obtain ⟨s, hs, t, ht, hne⟩ := F.nontrivial
    by_contra! h
    apply hne
    linarith [hs.1, hs.2, ht.1, ht.2]
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  let L := localCurveTheory_of_compact P.flow hcompactP
  have hBounds : CurveEvolutionAmbientBounds P.flow G.K0 G.K1 G.K2 :=
    G.product_bounds circumference hcirc
  have hest (T : ℝ) (hT : a < T) (_hTb : T ≤ b)
      (c : ℝ → ℝ → P.charts.Point) (hc : M63C2ShrinkingCurveOn P.flow c (Icc a T)) :
      M63C2CurveEstimates P.flow c T G.K0 G.K1 G.K2 :=
    c2_estimates_of_local hM62 P.flow hcompactP L G.nonnegative.1
      G.nonnegative.2.1 G.nonnegative.2.2 hBounds c hc hT
  have hglobal := smooth_ramp_existence_of_local P L G.nonnegative.1
    G.nonnegative.2.1 G.nonnegative.2.2 hBounds hest
  let gamma : LoopTwoSphere → ℝ → P.charts.Point :=
    fun z => m63CanonicalRamp P (periodicFreeLoop (A.family z))
  have hperiod (z : LoopTwoSphere) : Function.Periodic (gamma z) curvePeriod := by
    apply canonicalRamp_periodic P
    exact periodic_periodicFreeLoop (A.family z)
  have hspace (z : LoopTwoSphere) : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (3 + 1)) ∞ (gamma z) :=
    canonicalRamp_contMDiff P le_rfl (A.angular_smooth z)
  have hramps (z : LoopTwoSphere) : M63IsRampAt P (gamma z) a :=
    canonicalRamp_isRamp P ((A.angular_smooth z).mdifferentiable (by simp)) a
  choose c hc hinit hi hramp using fun z => hglobal (gamma z) (hperiod z) (hspace z) (hramps z)
  let c0 : LoopTwoSphere → ℝ → ℝ → P.charts.Point := fun z x _ => gamma z x
  obtain ⟨nu0, V0, B0, m, R0, hnu0, hV0, hB0, hm, hR0, hinitial⟩ :=
    exists_canonicalRamp_initial_family_bounds F hcompact A P
  have hspeed (z : LoopTwoSphere) :
      curveSpeed P.flow (c z) a = curveSpeed P.flow (c0 z) a :=
    funext fun x => curveSpeed_congr_slice P.flow (hinit z) (x := x)
  have hinitialSpeed (z : LoopTwoSphere) (x : ℝ) :
      nu0 ≤ curveSpeed P.flow (c z) a x ∧ curveSpeed P.flow (c z) a x ≤ V0 := by
    rw [hspeed z]
    exact ⟨(hinitial z x).1, (hinitial z x).2.1⟩
  have hinitialGradient (z : LoopTwoSphere) (x : ℝ) :
      |deriv (curveSpeed P.flow (c z) a) x| ≤ B0 := by
    rw [hspeed z]
    exact (hinitial z x).2.2.1
  let C := m62C1 G.K0 G.K1 G.K2
  have hC : 0 ≤ C := by
    have h0 := G.nonnegative.1
    have h1 := G.nonnegative.2.1
    have h2 := G.nonnegative.2.2
    dsimp only [C, m62C1, m62C0]
    positivity
  let coeff := C * Real.exp (G.K2 * (b - a)) / m
  have hcoeff : 0 ≤ coeff := by dsimp only [coeff]; positivity
  let K := (R0 + coeff * (b - a)) * Real.exp ((C + G.K2) * (b - a))
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg (add_nonneg hR0 (mul_nonneg hcoeff (sub_nonneg.mpr hab.le)))
      (Real.exp_pos _).le
  have hcurvature (z : LoopTwoSphere) (t : ℝ) (ht : t ∈ Icc a b) (x : ℝ) :
      m62Curvature P.flow (c z) t x ≤ K := by
    have hmin (y : ℝ) : m ≤ m62Slope P (c z) a y := by
      rw [slope_congr_slice P (c := c z) (d := c0 z) (hinit z)]
      exact (hinitial z y).2.2.2.1
    have hmax (y : ℝ) : m63RampRatio P (c z) 1 a y ≤ R0 := by
      rw [rampRatio_congr_slice P (c := c z) (d := c0 z) (hinit z)]
      exact (hinitial z y).2.2.2.2
    have hbound := c2_rampCurvature_bound P L (c z) (m63C2_of_m62 (hc z)) hab
      G.nonnegative.1 G.nonnegative.2.1 G.nonnegative.2.2 hBounds
      (hest b hab le_rfl (c z) (m63C2_of_m62 (hc z))) hm hmin hmax t ht x
    apply hbound.trans
    have htime : t - a ≤ b - a := sub_le_sub_right ht.2 a
    have hsum : R0 + coeff * (t - a) ≤ R0 + coeff * (b - a) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left htime hcoeff)
    have hexp : Real.exp ((C + G.K2) * (t - a)) ≤
        Real.exp ((C + G.K2) * (b - a)) :=
      Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left htime (add_nonneg hC G.nonnegative.2.2))
    exact mul_le_mul hsum hexp (Real.exp_pos _).le
      (add_nonneg hR0 (mul_nonneg hcoeff (sub_nonneg.mpr hab.le)))
  have hcurvatureSq (z : LoopTwoSphere) (t : ℝ) (ht : t ∈ Ioo a b) (x : ℝ) :
      m62CurvatureSquared P.flow (c z) t x ≤ K ^ 2 := by
    rw [← M62.curvature_sq]
    have hbound := hcurvature z t ⟨ht.1.le, ht.2.le⟩ x
    simpa only [pow_two] using
      mul_le_mul hbound hbound (M62.curvature_nonneg P.flow (c z) t x) hK
  obtain ⟨N, e, he, heClosed, heInjective⟩ :=
    exists_embedding_euclidean_of_compact («I» := 𝓡 (3 + 1)) (M := P.charts.Point)
  obtain ⟨U, rho, hU, heU, hrho, hrhoe, _hmin, _hunique⟩ :=
    exists_smooth_compact_embedded_retraction e heClosed he heInjective
  let W := EuclideanSpace ℝ (Fin N)
  obtain ⟨hj0, hj1, hj2⟩ := continuous_canonicalRamp_embedded_initial_jets F hcompact A P he

  let Z := ULift.{u} LoopTwoSphere
  let liftHomeo : Z ≃ₜ LoopTwoSphere := Homeomorph.ulift
  let : CompactSpace Z := liftHomeo.symm.compactSpace
  have hdown : Continuous (fun z : Z => z.down) := liftHomeo.continuous
  have hup : Continuous (fun z : LoopTwoSphere => (ULift.up z : Z)) :=
    liftHomeo.symm.continuous
  have hinitialFun (z : LoopTwoSphere) :
      (fun x => e (c z x a)) = fun x => e (gamma z x) :=
    funext fun x => congrArg e (hinit z x)
  have hz0 : Continuous (fun z : Z × ℝ => e (c z.1.down z.2 a)) := by
    apply (hj0.comp ((hdown.comp continuous_fst).prodMk continuous_snd)).congr
    intro z
    exact congrArg e (hinit z.1.down z.2).symm
  have hz1 : Continuous (fun z : Z × ℝ =>
      deriv (fun y => e (c z.1.down y a)) z.2) := by
    apply (hj1.comp ((hdown.comp continuous_fst).prodMk continuous_snd)).congr
    intro z
    exact congrArg (fun f : ℝ → W => deriv f z.2) (hinitialFun z.1.down).symm
  have hz2 : Continuous (fun z : Z × ℝ =>
      deriv (deriv (fun y => e (c z.1.down y a))) z.2) := by
    apply (hj2.comp ((hdown.comp continuous_fst).prodMk continuous_snd)).congr
    intro z
    exact congrArg (fun f : ℝ → W => deriv (deriv f) z.2) (hinitialFun z.1.down).symm
  obtain ⟨hwhole0, hwhole1, hwhole2⟩ :=
    continuous_family_embedded_threeJets_of_curvature_bound P.flow hcompactP
      he hU heU hrho hrhoe (fun z : Z => c z.down) (fun z => hc z.down)
      hz0 hz1 hz2 (sq_nonneg K) hnu0 hV0 hB0
      (fun z => hinitialSpeed z.down) (fun z => hinitialGradient z.down)
      (fun z => hcurvatureSq z.down)
  let T := Icc a b × LoopTwoSphere
  let reorder : T × ℝ → (Z × ℝ) × Icc a b :=
    fun w => ((ULift.up w.1.2, w.2), w.1.1)
  have hreorder : Continuous reorder :=
    ((hup.comp continuous_fst.snd).prodMk continuous_snd).prodMk continuous_fst.fst
  have hslice (w : T) :
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 (3 + 1)) 2 (fun x => c w.2 x w.1) :=
    (hc w.2).spatial_regular w.1 w.1.2
  obtain ⟨hvalue, hangularFirst, _hangularSecond⟩ :=
    continuous_angular_jets_of_embedded_jets P.flow (fun w : T => (w.1 : ℝ))
      (continuous_subtype_val.comp continuous_fst) (fun w => w.1.2)
      (fun w x => c w.2 x w.1) hslice he hU heU hrho hrhoe
      (hwhole0.comp hreorder) (hwhole1.comp hreorder) (hwhole2.comp hreorder)
  have hdegree (z : LoopTwoSphere) (t : ℝ) (ht : t ∈ Icc a b) :
      ∃ lift : M63PositiveDegreeLift P (fun x => c z x t), lift.degree = 1 := by
    have hinitialDegree : ∃ lift : M63PositiveDegreeLift P (fun x => c z x a),
        lift.degree = 1 := by
      rw [show (fun x => c z x a) = gamma z from funext (hinit z)]
      exact canonicalRamp_degree_one P (periodicFreeLoop (A.family z))
    obtain ⟨lift, hlift⟩ := hinitialDegree
    obtain ⟨other, hother⟩ := m63PositiveDegree_preserved P (c z) (hc z).continuous
      (hc z).periodic (hc z).spatial_regular (hramp z) lift ht
    exact ⟨other, hother.trans hlift⟩
  let beta : T → ℝ → M := fun w x => (c w.2 x w.1).1
  let := P.charts.chartedSpace
  let := P.circle.chartedSpace
  have hproj : ContMDiff (𝓡 (3 + 1)) (𝓡 3) ∞ (Prod.fst : P.charts.Point → M) :=
    contMDiff_fst.comp P.charts.to_product_smooth
  have hbetaSpace (w : T) : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 (beta w) :=
    (hproj.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)).comp
      ((hslice w).of_le (by norm_num))
  have hbetaPeriod (w : T) : Function.Periodic (beta w) curvePeriod :=
    fun x => congrArg Prod.fst ((hc w.2).periodic w.1 w.1.2 x)
  have hbetaValue : Continuous (fun w : T × ℝ => beta w.1 w.2) := hvalue.fst
  have hbetaFirst : Continuous (fun w : T × ℝ =>
      m63AngularFirstJet (n := 3) (beta w.1) w.2) := by
    apply ((hproj.continuous_tangentMap
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)).comp hangularFirst).congr
    intro w
    have hchain := mfderiv_comp_apply (f := fun x => c w.1.2 x w.1.1)
      (g := (Prod.fst : P.charts.Point → M)) w.2
      (hproj.mdifferentiableAt (by simp))
      ((hslice w.1 w.2).mdifferentiableAt (by norm_num)) (1 : ℝ)
    apply TotalSpace.ext
    · rfl
    · exact heq_of_eq hchain.symm
  obtain ⟨can, hcan⟩ := exists_continuous_c1Loop_family_of_periodic
    beta hbetaPeriod hbetaSpace hbetaValue hbetaFirst

  let projectedValue : T → C1FreeLoopSpace (M := M) := fun w =>
    if (w.1 : ℝ) = a then A.family w.2 else can w
  have hprojectedInitial (z : LoopTwoSphere) :
      projectedValue (⟨a, ha⟩, z) = A.family z := by
    simp only [projectedValue, if_true]
  have hprojectedAngular (w : T) (x : ℝ) :
      periodicFreeLoop (projectedValue w) x = beta w x := by
    dsimp only [projectedValue]
    split_ifs with ht
    · change periodicFreeLoop (A.family w.2) x = (c w.2 x w.1).1
      rw [ht, hinit w.2 x]
      rfl
    · exact hcan w x
  have hsame (w : T) (q : LoopCircle) :
      projectedValue w q = can w q ∧
        c1LoopTangent (projectedValue w) q = c1LoopTangent (can w) q := by
    obtain ⟨x, _hx, hxq⟩ := exists_angularPoint q
    have hq : (⟨angularPoint x, norm_angularPoint x⟩ : LoopCircle) = q :=
      Subtype.ext hxq
    have heq : periodicFreeLoop (projectedValue w) = periodicFreeLoop (can w) :=
      funext fun y => (hprojectedAngular w y).trans (hcan w y).symm
    have hboundary (loop : C1FreeLoopSpace (M := M)) :
        periodicFreeLoop loop x = loop q := by
      change loop.extension (angularPoint x) = loop q
      rw [← hq]
      exact loop.boundary ⟨angularPoint x, norm_angularPoint x⟩
    constructor
    · exact (hboundary (projectedValue w)).symm.trans
        ((congrFun heq x).trans (hboundary (can w)))
    · have hj (loop : C1FreeLoopSpace (M := M)) :
          m63AngularFirstJet (periodicFreeLoop loop) x = c1LoopTangent loop q := by
        simpa only [hq] using m63AngularFirstJet_eq_c1LoopTangent loop x
      rw [← hj (projectedValue w), ← hj (can w), heq]
  have hprojected : Continuous projectedValue := by
    have hcontinuous := (continuous_iff_values_tangents _).mp can.continuous
    apply (continuous_iff_values_tangents projectedValue).mpr
    constructor
    · exact hcontinuous.1.congr (fun w => ContinuousMap.ext (fun q => (hsame w q).1.symm))
    · exact hcontinuous.2.congr (fun w => ContinuousMap.ext (fun q => (hsame w q).2.symm))
  let projected : Icc a b → C(LoopTwoSphere, C1FreeLoopSpace (M := M)) :=
    fun t => ⟨fun z => projectedValue (t, z),
      hprojected.comp (continuous_const.prodMk continuous_id)⟩
  have hinitialProjected (ha' : a ∈ Icc a b) : projected ⟨a, ha'⟩ = A.family := by
    apply ContinuousMap.ext
    intro z
    change projectedValue (⟨a, ha'⟩, z) = A.family z
    simp only [projectedValue, if_true]
  have hnull (t : Icc a b) (z : LoopTwoSphere) :
      IsNullHomotopicLoop (projected t z) := by
    have htime (s : I) : (t : ℝ) + (s : ℝ) * (a - t) ∈ Icc a b := by
      have hleft := mul_nonneg s.2.1 (sub_nonneg.mpr t.2.1)
      have hright := mul_nonneg (sub_nonneg.mpr s.2.2) (sub_nonneg.mpr t.2.1)
      constructor <;> nlinarith only [hleft, hright, t.2.2]
    let timePath : I → Icc a b := fun s => ⟨t + (s : ℝ) * (a - t), htime s⟩
    have htimeContinuous : Continuous timePath :=
      (continuous_const.add (continuous_subtype_val.mul continuous_const)).subtype_mk _
    have hstart : timePath 0 = t := Subtype.ext (by simp [timePath])
    have hfinish : timePath 1 = ⟨a, ha⟩ := Subtype.ext (by simp [timePath])
    let path : Path (projected t z) (A.family z) :=
      ⟨⟨fun s => projectedValue (timePath s, z),
        hprojected.comp (htimeContinuous.prodMk continuous_const)⟩,
        congrArg (fun r => projectedValue (r, z)) hstart,
        (congrArg (fun r => projectedValue (r, z)) hfinish).trans (hprojectedInitial z)⟩
    exact m59NullLoop_of_path path (A.null_family z)
  let reorderRecord : LoopTwoSphere × ℝ × Icc a b → T × ℝ :=
    fun w => ((w.2.2, w.1), w.2.1)
  have hreorderRecord : Continuous reorderRecord :=
    (continuous_snd.snd.prodMk continuous_fst).prodMk continuous_snd.fst
  exact ⟨{
    curve := c
    shrinking := hc
    intrinsic_regular := hi
    initial_eq := hinit
    ramp := hramp
    degree_one := hdegree
    value_continuous := hvalue.comp hreorderRecord
    velocity_continuous := hangularFirst.comp hreorderRecord
    projected := projected
    projected_continuous := hprojected
    projected_eq := fun t z x => hprojectedAngular (t, z) x
    projected_initial := hinitialProjected
    projected_null := hnull }⟩

end PoincareConjecture
