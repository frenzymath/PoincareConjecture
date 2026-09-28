import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceNormalCurvatureLimit
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceNormalFirstLimits










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M63

open SpectralHeatNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b L S R m0 V0 : ℝ} [Fact (0 < L)]

local notation "W" => EuclideanSpace ℝ ι
local notation "StateV" => State ((ℤ × Fin 2) × ι)
local notation "X" => C(AddCircle L, W)
local notation "Y" => C(AddCircle curvePeriod, W)




theorem exists_closed_normal_geometric_fields_of_spectral_family
    (F : RicciFlow n M (Icc a b)) (hcompact : IsCompact (univ : Set M))
    (hS : 0 < S) (hSone : S ≤ 1) (hSb : a + S < b)
    (hR : 0 ≤ R) (hm0 : 0 < m0) (hmV : m0 ≤ V0)
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p)
    (Vn : ℕ → C(Icc (0 : ℝ) S, StateV)) (V : C(Icc (0 : ℝ) S, StateV))
    (D : ℕ → C(Icc (0 : ℝ) S, C(AddCircle L, ℝ)))
    (d : C(Icc (0 : ℝ) S, C(AddCircle L, ℝ)))
    (psi : ℕ → ℝ → ℝ → ℝ) (c : ℕ → ℝ → ℝ → M) (vinit : ℕ → ℝ)
    (hV : Tendsto Vn atTop (𝓝 V)) (hD : Tendsto D atTop (𝓝 d))
    (hphase : ∀ j (t : Icc (0 : ℝ) S), DifferentiableAt ℝ
      (fun r : ℝ => vectorPeriodicSpectralTranslation (L := L) r (Vn j t)) 0) :
    let _ : Fact (0 < curvePeriod) := ⟨by unfold curvePeriod; positivity⟩
    let E := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm
    let D0 := (E.toContinuousLinearMap.compLeftContinuous ℝ (AddCircle L)).comp
      (vectorPeriodicJet (L := L) 1 0 (by omega))
    let D1 := (E.toContinuousLinearMap.compLeftContinuous ℝ (AddCircle L)).comp
      (vectorPeriodicJet (L := L) 1 1 (by omega))
    let qn := fun j (t : Icc (0 : ℝ) S) (x : ℝ) => D0 (Vn j t) (x : AddCircle L)
    let pn := fun j (t : Icc (0 : ℝ) S) (x : ℝ) => D1 (Vn j t) (x : AddCircle L)
    let q := fun (t : Icc (0 : ℝ) S) (x : ℝ) => D0 (V t) (x : AddCircle L)
    let p := fun (t : Icc (0 : ℝ) S) (x : ℝ) => D1 (V t) (x : AddCircle L)
    let t0 : Icc (0 : ℝ) S := ⟨0, le_rfl, hS.le⟩
    let f := q t0
    (∀ j t x, qn j t x ∈ U ∧
      mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (qn j t x) (pn j t x) ≠ 0) →
    (∀ j t x, qn j t x = e (ρ (qn j t x))) →
    (∀ t x, q t x ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (q t x) (p t x) ≠ 0) →
    ContDiff ℝ 2 f →
    (∀ eps > 0, ∃ N : ℕ, ∀ j ≥ N, ∀ x,
      ‖deriv (deriv (qn j t0)) x - deriv (deriv f) x‖ < eps) →
    ∀ ell : ℝ, 0 < ell →
    (∀ j (t : Icc (0 : ℝ) S), ContDiff ℝ 1 (psi j t)) →
    (∀ j (t : Icc (0 : ℝ) S) x, ell ≤ deriv (psi j t) x) →
    (∀ j (t : Icc (0 : ℝ) S) (x : ℝ), D j t (x : AddCircle L) = psi j t x - x) →
    (∀ j x, psi j 0 x = x) →
    (∀ j, M62ShrinkingCurve F (c j)) →
    (∀ j, vinit j ∈ Icc m0 V0) →
    (∀ j x, curveSpeed F (c j) a x = vinit j) →
    (∀ j t, t ∈ Ioo a b → ∀ x, m62CurvatureSquared F (c j) t x ≤ R) →
    (∀ j (t : Icc (0 : ℝ) S) x,
      c j x (a + t) = ρ (qn j t (psi j t ((L / curvePeriod) * x)))) →
    d t0 = 0 →
    ∃ (Rn Sn Hn : ℕ → C(Icc a (a + S), Y)) (r s h : C(Icc a (a + S), Y)),
      Tendsto Rn atTop (𝓝 r) ∧ Tendsto Sn atTop (𝓝 s) ∧ Tendsto Hn atTop (𝓝 h) ∧
      (∀ j (t : Icc a (a + S)) (x : ℝ),
        Rn j t (x : AddCircle curvePeriod) = e (c j x t)) ∧
      (∀ j (t : Icc a (a + S)) (x : ℝ), Sn j t (x : AddCircle curvePeriod) =
        mfderiv (𝓡 n) 𝓘(ℝ, W) e (c j x t) (spatialUnitTangent F (c j) t x)) ∧
      (∀ j (t : Icc a (a + S)) (x : ℝ), Hn j t (x : AddCircle curvePeriod) =
        mfderiv (𝓡 n) 𝓘(ℝ, W) e (c j x t) (m62CurvatureVector F (c j) t x)) ∧
      (∀ (t : Icc a (a + S)) z, r t z ∈ U) ∧
      ∀ x : ℝ, r ⟨a, le_rfl, le_add_of_nonneg_right hS.le⟩ (x : AddCircle curvePeriod) =
        f ((L / curvePeriod) * x) := by
  classical
  let : Fact (0 < curvePeriod) := ⟨by unfold curvePeriod; positivity⟩
  dsimp only
  intro hguard hfixed hguard0 hf hsecond ell hell hpsi hderiv hDrep hpsi0 hc
    hvinit hinitial hcurv hslice hd0
  let E := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm
  let D0 : StateV →L[ℝ] X :=
    (E.toContinuousLinearMap.compLeftContinuous ℝ (AddCircle L)).comp
      (vectorPeriodicJet (L := L) 1 0 (by omega))
  let D1 : StateV →L[ℝ] X :=
    (E.toContinuousLinearMap.compLeftContinuous ℝ (AddCircle L)).comp
      (vectorPeriodicJet (L := L) 1 1 (by omega))
  let Q := fun j => D0.compLeftContinuous ℝ (Icc (0 : ℝ) S) (Vn j)
  let P := fun j => D1.compLeftContinuous ℝ (Icc (0 : ℝ) S) (Vn j)
  let q := D0.compLeftContinuous ℝ (Icc (0 : ℝ) S) V
  let p := D1.compLeftContinuous ℝ (Icc (0 : ℝ) S) V
  have hQ : Tendsto Q atTop (𝓝 q) :=
    (D0.compLeftContinuous ℝ (Icc (0 : ℝ) S)).continuous.tendsto V |>.comp hV
  have hP : Tendsto P atTop (𝓝 p) :=
    (D1.compLeftContinuous ℝ (Icc (0 : ℝ) S)).continuous.tendsto V |>.comp hV
  obtain ⟨_hfirst0, _secondFields, hjets, _hjetlim⟩ :=
    exists_spectral_approximation_jets Vn V hV hphase
  have hQguard (j : ℕ) (t : Icc (0 : ℝ) S) (z : AddCircle L) :
      Q j t z ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (Q j t z) (P j t z) ≠ 0 := by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    exact hguard j t x
  have hqguard (t : Icc (0 : ℝ) S) (z : AddCircle L) :
      q t z ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (q t z) (p t z) ≠ 0 := by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    exact hguard0 t x
  have hQfixed (j : ℕ) (t : Icc (0 : ℝ) S) (z : AddCircle L) :
      Q j t z = e (ρ (Q j t z)) := by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    exact hfixed j t x
  obtain ⟨R0, S0, r0, s0, hR0, hS0, hR0rep, hS0rep, hvalue⟩ :=
    exists_closed_normal_value_unitTangent_limits F hS hSb.le he hU heU hρ hρe
      Q P q p D d psi c hQ hP hD (fun j t x => (hjets j t).2.1 x)
      hQguard hqguard hQfixed hpsi (fun j t x => hell.trans_le (hderiv j t x))
      hDrep hslice
  obtain ⟨Hreal, hreal, _hinit, hHcont, hHrep, _hinitrep, _hHstart,
      hhcont, _hhstart, hHlim, _htrace⟩ :=
    exists_closed_normalCurvature_limit_of_spectral_family F hcompact hS hSone hSb
      hR hm0 hmV he hU heU hρ hρe Vn V D d psi c vinit hV hD hphase
      hguard hfixed hguard0 hf hsecond ell hell hpsi hderiv hDrep hpsi0
      hc hvinit hinitial hcurv hslice
  let shift : C(Icc a (a + S), Icc (0 : ℝ) S) :=
    ⟨fun t => ⟨t - a, sub_nonneg.mpr t.property.1, by linarith only [t.property.2]⟩,
      (continuous_subtype_val.sub continuous_const).subtype_mk _⟩
  have htime (t : Icc a (a + S)) : a + (shift t : ℝ) = t := by
    change a + ((t : ℝ) - a) = t
    ring
  let Rn := fun j => (R0 j).comp shift
  let Sn := fun j => (S0 j).comp shift
  let r := r0.comp shift
  let s := s0.comp shift
  let Hn : ℕ → C(Icc a (a + S), Y) := fun j => ⟨_, (hHcont j).domRestrict⟩
  let h : C(Icc a (a + S), Y) := ⟨_, hhcont.domRestrict⟩
  have hRn : Tendsto Rn atTop (𝓝 r) := (shift.continuous_precomp.tendsto r0).comp hR0
  have hSn : Tendsto Sn atTop (𝓝 s) := (shift.continuous_precomp.tendsto s0).comp hS0
  have hHn : Tendsto Hn atTop (𝓝 h) :=
    (hhcont.tendsto_domRestrict_iff_tendstoUniformlyOn hHcont).mpr hHlim
  refine ⟨Rn, Sn, Hn, r, s, h, hRn, hSn, hHn, ?_, ?_, ?_, ?_, ?_⟩
  · intro j t x
    change R0 j (shift t) (x : AddCircle curvePeriod) = e (c j x t)
    simpa only [htime] using hR0rep j (shift t) x
  · intro j t x
    change S0 j (shift t) (x : AddCircle curvePeriod) = _
    refine (hS0rep j (shift t) x).trans ?_
    exact congrArg (fun u : ℝ => (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c j x u)
      (spatialUnitTangent F (c j) u x) : W)) (htime t)
  · intro j t x
    exact hHrep j t t.property x
  · intro t z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    change r0 (shift t) (x : AddCircle curvePeriod) ∈ U
    rw [(hvalue (shift t) x).1]
    exact (hqguard (shift t) _).1
  · intro x
    let ta : Icc a (a + S) := ⟨a, le_rfl, le_add_of_nonneg_right hS.le⟩
    let t0 : Icc (0 : ℝ) S := ⟨0, le_rfl, hS.le⟩
    have hshift : shift ta = t0 := by
      apply Subtype.ext
      change a - a = 0
      exact sub_self a
    change r0 (shift ta) (x : AddCircle curvePeriod) = _
    rw [hshift, (hvalue t0 x).1]
    change d t0 = 0 at hd0
    rw [hd0]
    simp only [ContinuousMap.zero_apply, add_zero]
    rfl

end PoincareConjecture.M63
