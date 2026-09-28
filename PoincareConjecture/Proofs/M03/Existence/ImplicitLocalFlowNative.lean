import PoincareConjecture.Proofs.M03.Existence.ContinuousPathCompositionNative
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.ContinuousMap.Interval








set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace PoincareConjecture.ImplicitLocalFlowNative

theorem exists_contDiff_implicit_on
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {k : ℕ∞} (f : X × Y → Y) (hf : ContDiff ℝ k f) (hk : k ≠ 0) (b : X × Y)
    (hinv : (fderiv ℝ f b ∘L ContinuousLinearMap.inr ℝ X Y).IsInvertible) :
    ∃ U : X → Y, ∃ S : Set X,
      IsOpen S ∧ b.1 ∈ S ∧ ContDiffOn ℝ k U S ∧ U b.1 = b.2 ∧
      (∀ x ∈ S, f (x, U x) = f b) ∧
      ∀ᶠ v in 𝓝 b, f v = f b → U v.1 = v.2 := by
  have hk' : (k : ℕ∞ω) ≠ 0 := by exact_mod_cast hk
  let D : ImplicitFunctionData ℝ (X × Y) Y X :=
    (hf.contDiffAt.hasStrictFDerivAt hk').implicitFunctionDataOfProdDomain hinv
  let H := D.toOpenPartialHomeomorph
  have hD : ContDiff ℝ k D.prodFun := hf.prodMk contDiff_fst
  obtain ⟨e, he⟩ := D.isInvertible_fderiv_prodFun
  have heN := e.nhds
  rw [he] at heN
  have hN : {v : X × Y | (fderiv ℝ D.prodFun v).IsInvertible} ∈ 𝓝 b :=
    (hD.continuous_fderiv hk').continuousAt.preimage_mem_nhds heN
  obtain ⟨V, hV, hVo, hbV⟩ := mem_nhds_iff.mp hN
  let G := H.restrOpen V hVo
  have hbG : b ∈ G.source := ⟨D.pt_mem_toOpenPartialHomeomorph_source, hbV⟩
  let S : Set X := (fun x => (f b, x)) ⁻¹' G.target
  let U : X → Y := fun x => (G.symm (f b, x)).2
  have hSo : IsOpen S := G.open_target.preimage (continuous_const.prodMk continuous_id)
  have hbS : b.1 ∈ S := G.map_source hbG
  have hUb : U b.1 = b.2 := congrArg Prod.snd (G.left_inv hbG)
  have hU : ContDiffOn ℝ k U S := by
    intro x hx
    have hback := G.map_target hx
    obtain ⟨e', he'⟩ := hV hback.2
    have hder : HasFDerivAt G (e' : (X × Y) →L[ℝ] Y × X)
        (G.symm (f b, x)) := by
      change HasFDerivAt D.prodFun _ _
      rw [he']
      exact (hD.differentiable hk' _).hasFDerivAt
    have hi : ContDiffAt ℝ k G.symm (f b, x) :=
      G.contDiffAt_symm hx hder hD.contDiffAt
    exact ((hi.comp x (contDiffAt_const.prodMk contDiffAt_id)).snd).contDiffWithinAt
  refine ⟨U, S, hSo, hbS, hU, hUb, ?_, ?_⟩
  · intro x hx
    have hright := G.right_inv hx
    have hfirst : (G.symm (f b, x)).1 = x := congrArg Prod.snd hright
    have hvalue : f (G.symm (f b, x)) = f b := congrArg Prod.fst hright
    have hpair : (x, U x) = G.symm (f b, x) := Prod.ext hfirst.symm rfl
    rw [hpair]
    exact hvalue
  · filter_upwards [G.open_source.mem_nhds hbG] with v hv hval
    have hleft := congrArg Prod.snd (G.left_inv hv)
    change (G.symm (f v, v.1)).2 = v.2 at hleft
    simpa only [hval] using hleft

theorem exists_smooth_implicit_on
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (f : X × Y → Y) (hf : ContDiff ℝ ∞ f) (b : X × Y)
    (hinv : (fderiv ℝ f b ∘L ContinuousLinearMap.inr ℝ X Y).IsInvertible) :
    ∃ U : X → Y, ∃ S : Set X,
      IsOpen S ∧ b.1 ∈ S ∧ ContDiffOn ℝ ∞ U S ∧ U b.1 = b.2 ∧
      (∀ x ∈ S, f (x, U x) = f b) ∧
      ∀ᶠ v in 𝓝 b, f v = f b → U v.1 = v.2 :=
  exists_contDiff_implicit_on f hf (by simp) b hinv

abbrev UnitInterval := Icc (0 : ℝ) 1

def unitZero : UnitInterval := ⟨0, le_rfl, zero_le_one⟩

def unitOne : UnitInterval := ⟨1, zero_le_one, le_rfl⟩

def unitParameter : C(UnitInterval, ℝ) := ⟨Subtype.val, continuous_subtype_val⟩

def unitProjection : C(ℝ, UnitInterval) :=
  ⟨projIcc 0 1 zero_le_one, continuous_projIcc⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

abbrev Path (E : Type*) [TopologicalSpace E] := C(UnitInterval, E)

def extendPath (u : Path E) : C(ℝ, E) := u.comp unitProjection

@[simp] theorem extendPath_apply_coe (u : Path E) (s : UnitInterval) :
    extendPath u s = u s := by
  change u (projIcc 0 1 zero_le_one s) = u s
  congr 1
  exact Subtype.ext (by simp [projIcc, s.property.1, s.property.2])

def pathIntegral (u : Path E) : Path E :=
  ⟨fun s => ∫ r in (0 : ℝ)..(s : ℝ), extendPath u r,
    (intervalIntegral.differentiable_integral_of_continuous
      (extendPath u).continuous).continuous.comp continuous_subtype_val⟩

@[simp] theorem pathIntegral_apply (u : Path E) (s : UnitInterval) :
    pathIntegral u s = ∫ r in (0 : ℝ)..(s : ℝ), extendPath u r := rfl

@[simp] theorem pathIntegral_zero (u : Path E) : pathIntegral u unitZero = 0 := by
  simp [pathIntegral, unitZero]

theorem norm_pathIntegral_le (u : Path E) : ‖pathIntegral u‖ ≤ ‖u‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro s
  calc
    ‖pathIntegral u s‖ ≤ ‖u‖ * |(s : ℝ) - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const
        (fun r _ => u.norm_coe_le_norm (unitProjection r))
    _ ≤ ‖u‖ * 1 := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa only [sub_zero, abs_of_nonneg s.property.1] using s.property.2
    _ = ‖u‖ := mul_one _

def pathIntegralCLM : Path E →L[ℝ] Path E :=
  LinearMap.mkContinuous
    { toFun := pathIntegral
      map_add' := by
        intro u v
        ext s
        exact intervalIntegral.integral_add
          ((extendPath u).continuous.intervalIntegrable _ _)
          ((extendPath v).continuous.intervalIntegrable _ _)
      map_smul' := by
        intro c u
        ext s
        exact intervalIntegral.integral_smul c (extendPath u) }
    1 (fun u => by simpa using norm_pathIntegral_le u)

@[simp] theorem pathIntegralCLM_apply (u : Path E) : pathIntegralCLM u = pathIntegral u := rfl

abbrev Parameters (E : Type*) := ℝ × (ℝ × E)

def timePath (q : Parameters E) : Path ℝ :=
  ContinuousMap.const UnitInterval q.1 + q.2.1 • unitParameter

def spacetimePath (q : Parameters E × Path E) : Path (ℝ × E) :=
  (ContinuousLinearMap.inl ℝ ℝ E).compLeftContinuous ℝ UnitInterval (timePath q.1) +
    (ContinuousLinearMap.inr ℝ ℝ E).compLeftContinuous ℝ UnitInterval q.2

@[simp] theorem spacetimePath_apply (q : Parameters E × Path E) (s : UnitInterval) :
    spacetimePath q s = (q.1.1 + q.1.2.1 * s, q.2 s) := by
  simp [spacetimePath, timePath, unitParameter]

theorem contDiff_timePath : ContDiff ℝ ∞ (timePath (E := E)) := by
  exact ((ContinuousLinearMap.const ℝ UnitInterval : ℝ →L[ℝ] Path ℝ).contDiff.comp
    contDiff_fst).add
    (contDiff_snd.fst.smul contDiff_const)

theorem contDiff_spacetimePath : ContDiff ℝ ∞ (spacetimePath (E := E)) := by
  exact (((ContinuousLinearMap.inl ℝ ℝ E).compLeftContinuous ℝ UnitInterval).contDiff.comp
    (contDiff_timePath.comp contDiff_fst)).add
      (((ContinuousLinearMap.inr ℝ ℝ E).compLeftContinuous ℝ UnitInterval).contDiff.comp
        contDiff_snd)

def residual (f : C(ℝ × E, E)) (q : Parameters E × Path E) : Path E :=
  q.2 - ContinuousMap.const UnitInterval q.1.2.2 -
    q.1.2.1 • pathIntegral (f.comp (spacetimePath q))

theorem contDiff_residual_of_order {k : ℕ∞} (f : C(ℝ × E, E))
    (hf : ContDiff ℝ k (f : ℝ × E → E)) :
    ContDiff ℝ k (residual f) := by
  have hsource :=
    (ContinuousPathCompositionNative.contDiff_postcomp_of_order UnitInterval f hf).comp
      (contDiff_spacetimePath.of_le (WithTop.coe_le_coe.mpr le_top))
  exact (contDiff_snd.sub
    ((ContinuousLinearMap.const ℝ UnitInterval).contDiff.comp contDiff_fst.snd.snd)).sub
      (contDiff_fst.snd.fst.smul (pathIntegralCLM.contDiff.comp hsource))

theorem contDiff_residual (f : C(ℝ × E, E)) (hf : ContDiff ℝ ∞ (f : ℝ × E → E)) :
    ContDiff ℝ ∞ (residual f) :=
  contDiff_residual_of_order f hf

@[simp] theorem residual_zero_time (f : C(ℝ × E, E)) (a : ℝ) (x : E) (u : Path E) :
    residual f ((a, (0, x)), u) = u - ContinuousMap.const UnitInterval x := by
  simp [residual]

set_option backward.isDefEq.respectTransparency false in
theorem residual_partial_zero_time_of_order {k : ℕ∞} (f : C(ℝ × E, E))
    (hf : ContDiff ℝ k (f : ℝ × E → E)) (hk : k ≠ 0) (a : ℝ) (x : E) :
    fderiv ℝ (residual f) ((a, (0, x)), ContinuousMap.const UnitInterval x) ∘L
      ContinuousLinearMap.inr ℝ (Parameters E) (Path E) =
        ContinuousLinearMap.id ℝ (Path E) := by
  have hfull := ((contDiff_residual_of_order f hf).differentiable (by exact_mod_cast hk)
    ((a, (0, x)), ContinuousMap.const UnitInterval x)).hasFDerivAt
  have hpartial := hfull.comp (ContinuousMap.const UnitInterval x)
    (hasFDerivAt_prodMk_right (a, (0, x)) (ContinuousMap.const UnitInterval x))
  have hsimple : HasFDerivAt (fun u : Path E => residual f ((a, (0, x)), u))
      (ContinuousLinearMap.id ℝ (Path E)) (ContinuousMap.const UnitInterval x) := by
    apply HasFDerivAt.of_isLittleOTVS
    exact (Asymptotics.IsLittleOTVS.zero _ _).congr_left fun u => by
      simp only [residual_zero_time, sub_self, sub_zero, ContinuousLinearMap.id_apply,
        Pi.zero_apply]
  exact hpartial.unique hsimple

theorem residual_partial_zero_time (f : C(ℝ × E, E))
    (hf : ContDiff ℝ ∞ (f : ℝ × E → E)) (a : ℝ) (x : E) :
    fderiv ℝ (residual f) ((a, (0, x)), ContinuousMap.const UnitInterval x) ∘L
      ContinuousLinearMap.inr ℝ (Parameters E) (Path E) =
        ContinuousLinearMap.id ℝ (Path E) :=
  residual_partial_zero_time_of_order f hf (by simp) a x

theorem exists_smooth_integral_path (f : C(ℝ × E, E))
    (hf : ContDiff ℝ ∞ (f : ℝ × E → E)) (a : ℝ) (x : E) :
    ∃ U : Parameters E → Path E,
      U (a, (0, x)) = ContinuousMap.const UnitInterval x ∧
      ContDiffAt ℝ ∞ U (a, (0, x)) ∧
      ∀ᶠ q in 𝓝 (a, (0, x)),
        U q = ContinuousMap.const UnitInterval q.2.2 +
          q.2.1 • pathIntegral (f.comp (spacetimePath (q, U q))) := by
  let b : Parameters E × Path E := ((a, (0, x)), ContinuousMap.const UnitInterval x)
  have hR : ContDiffAt ℝ ∞ (residual f) b := (contDiff_residual f hf).contDiffAt
  have hinv : (fderiv ℝ (residual f) b ∘L
      ContinuousLinearMap.inr ℝ (Parameters E) (Path E)).IsInvertible := by
    rw [residual_partial_zero_time f hf a x]
    exact ⟨ContinuousLinearEquiv.refl ℝ (Path E), rfl⟩
  let U := hR.implicitFunction (by simp) hinv
  refine ⟨U, hR.implicitFunction_apply_self (by simp) hinv,
    hR.contDiffAt_implicitFunction (by simp) hinv, ?_⟩
  filter_upwards [hR.eventually_apply_implicitFunction (by simp) hinv] with q hq
  have hzero : residual f (q, U q) = 0 := by
    simpa [b, residual_zero_time] using hq
  change U q - ContinuousMap.const UnitInterval q.2.2 -
    q.2.1 • pathIntegral (f.comp (spacetimePath (q, U q))) = 0 at hzero
  simpa only [add_comm] using sub_eq_iff_eq_add.mp (sub_eq_zero.mp hzero)

theorem exists_contDiff_integral_path_on {k : ℕ∞} (f : C(ℝ × E, E))
    (hf : ContDiff ℝ k (f : ℝ × E → E)) (hk : k ≠ 0) (a : ℝ) (x : E) :
    ∃ U : Parameters E → Path E, ∃ S : Set (Parameters E),
      IsOpen S ∧ (a, (0, x)) ∈ S ∧ ContDiffOn ℝ k U S ∧
      U (a, (0, x)) = ContinuousMap.const UnitInterval x ∧
      (∀ q ∈ S, U q = ContinuousMap.const UnitInterval q.2.2 +
        q.2.1 • pathIntegral (f.comp (spacetimePath (q, U q)))) ∧
      ∀ᶠ v in 𝓝 ((a, (0, x)), ContinuousMap.const UnitInterval x),
        residual f v = 0 → U v.1 = v.2 := by
  have hinv : (fderiv ℝ (residual f)
      ((a, (0, x)), ContinuousMap.const UnitInterval x) ∘L
      ContinuousLinearMap.inr ℝ (Parameters E) (Path E)).IsInvertible := by
    rw [residual_partial_zero_time_of_order f hf hk a x]
    exact ⟨ContinuousLinearEquiv.refl ℝ (Path E), rfl⟩
  obtain ⟨U, S, hSo, hb, hU, hUb, hEq, hUnique⟩ :=
    exists_contDiff_implicit_on (residual f) (contDiff_residual_of_order f hf) hk
      ((a, (0, x)), ContinuousMap.const UnitInterval x) hinv
  refine ⟨U, S, hSo, hb, hU, hUb, ?_, ?_⟩
  · intro q hq
    have hzero : residual f (q, U q) = 0 := by
      simpa only [residual_zero_time, sub_self] using hEq q hq
    change U q - ContinuousMap.const UnitInterval q.2.2 -
      q.2.1 • pathIntegral (f.comp (spacetimePath (q, U q))) = 0 at hzero
    simpa only [add_comm] using sub_eq_iff_eq_add.mp (sub_eq_zero.mp hzero)
  · simpa only [residual_zero_time, sub_self] using hUnique

theorem exists_smooth_integral_path_on (f : C(ℝ × E, E))
    (hf : ContDiff ℝ ∞ (f : ℝ × E → E)) (a : ℝ) (x : E) :
    ∃ U : Parameters E → Path E, ∃ S : Set (Parameters E),
      IsOpen S ∧ (a, (0, x)) ∈ S ∧ ContDiffOn ℝ ∞ U S ∧
      U (a, (0, x)) = ContinuousMap.const UnitInterval x ∧
      (∀ q ∈ S, U q = ContinuousMap.const UnitInterval q.2.2 +
        q.2.1 • pathIntegral (f.comp (spacetimePath (q, U q)))) ∧
      ∀ᶠ v in 𝓝 ((a, (0, x)), ContinuousMap.const UnitInterval x),
        residual f v = 0 → U v.1 = v.2 :=
  exists_contDiff_integral_path_on f hf (by simp) a x

end PoincareConjecture.ImplicitLocalFlowNative

end
