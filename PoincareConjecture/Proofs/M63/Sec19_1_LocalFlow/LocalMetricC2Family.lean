import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.GeometricArclengthFamily
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.LocalCompactSpectralPool
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.CountableNormalPoolCommonSlab
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.FixedLabelC2Transport
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.UniquenessFields
import PoincareConjecture.Proofs.M63.Mathlib.SpatialPartialDerivative
import PoincareConjecture.Proofs.M63.Mathlib.RetainedPoolContinuity
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.SpectralSequenceC2Limit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v w

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {Z : Type w} [MetricSpace Z] [CompactSpace Z]
  {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι

open SpectralHeatNative

omit [T2Space M] [CompactSpace Z] in
private theorem exists_centered_arclength_data
    (F : RicciFlow n M (Icc a b)) (hab : a < b)
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p)
    (gamma : Z → ℝ → M)
    (hperiod : ∀ z, Function.Periodic (gamma z) curvePeriod)
    (hC2 : ∀ z, ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 (gamma z))
    (himm : ∀ z x, curveVelocity (n := n) (gamma z) x ≠ 0)
    (hzero : Continuous (fun p : Z × ℝ => e (gamma p.1 p.2)))
    (hfirst : Continuous (fun p : Z × ℝ => deriv (fun y => e (gamma p.1 y)) p.2))
    (hsecond : Continuous (fun p : Z × ℝ =>
      deriv (deriv (fun y => e (gamma p.1 y))) p.2)) (z0 : Z) :
    ∃ L : ℝ, 0 < L ∧ ∃ (g : Z → ℝ → M) (m : Z → ℝ) (phi : Z → ℝ → ℝ),
      (∀ z, Function.Periodic (g z) L) ∧
      (∀ z, ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 (g z)) ∧
      (∀ z x, curveVelocity (n := n) (g z) x ≠ 0) ∧
      (∀ z x, curveSpeed F (fun y _ => g z y) a x = m z) ∧
      Continuous m ∧ m z0 = 1 ∧
      Continuous (fun z : Z × ℝ => e (g z.1 z.2)) ∧
      Continuous (fun z : Z × ℝ => deriv (fun y => e (g z.1 y)) z.2) ∧
      Continuous (fun z : Z × ℝ => deriv (deriv (fun y => e (g z.1 y))) z.2) ∧
      (∀ z, ContDiff ℝ 2 (phi z) ∧ (∀ x, 0 < deriv (phi z) x) ∧
        ∀ x, phi z (x + curvePeriod) = phi z x + curvePeriod) ∧
      Continuous (fun z : Z × ℝ => phi z.1 z.2) ∧
      Continuous (fun z : Z × ℝ => deriv (phi z.1) z.2) ∧
      Continuous (fun z : Z × ℝ => deriv (deriv (phi z.1)) z.2) ∧
      ∀ z x, g z ((L / curvePeriod) * phi z x) = gamma z x := by
  classical
  let mean := fun z =>
    (∫ x in (0 : ℝ)..curvePeriod, curveSpeed F (fun y _ => gamma z y) a x) / curvePeriod
  have hfamily := exists_continuous_geometric_arclength_family F
    (show a ∈ Icc a b from ⟨le_rfl, hab.le⟩) Real.two_pi_pos
    he hU heU hρ hρe gamma hperiod hC2 himm hzero hfirst hsecond
  dsimp only at hfamily
  obtain ⟨hmpos, hmc, phi, hphi, hphic, hphidc, hphiddc,
    _hpsic, _hpsidc, _hpsiddc, hnormal, hq0, hq1, hq2⟩ := hfamily
  let M0 := mean z0
  have hM0 : 0 < M0 := hmpos z0
  let L := curvePeriod * M0
  have hL : 0 < L := mul_pos Real.two_pi_pos hM0
  let gn : Z → ℝ → M := fun z y => gamma z ((phi z).symm y)
  let qn : Z → ℝ → W := fun z y => e (gn z y)
  let g : Z → ℝ → M := fun z y => gn z (y / M0)
  let m : Z → ℝ := fun z => mean z / M0
  have hscale (x : ℝ) : HasDerivAt (fun y : ℝ => y / M0) (1 / M0) x :=
    (hasDerivAt_id x).div_const M0
  have hscalePos : 0 < 1 / M0 := one_div_pos.mpr hM0
  have hgn (z : Z) : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 (gn z) := (hnormal z).2.1
  have hqreg (z : Z) : ContDiff ℝ 2 (qn z) :=
    ((he.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp (hgn z)).contDiff
  have hqder (z : Z) (x : ℝ) : HasDerivAt (qn z) (deriv (qn z) x) x :=
    ((hqreg z).differentiable (by norm_num) x).hasDerivAt
  have hqder2 (z : Z) (x : ℝ) : HasDerivAt (deriv (qn z))
      (deriv (deriv (qn z)) x) x :=
    (((hqreg z).deriv' (n := 1)).differentiable (by norm_num) x).hasDerivAt
  have hg1 (z : Z) (x : ℝ) :
      deriv (fun y => e (g z y)) x = (1 / M0) • deriv (qn z) (x / M0) := by
    have hd := (hqder z (x / M0)).scomp x (hscale x)
    simpa only [Function.comp_def, g, qn] using hd.deriv
  have hg2 (z : Z) (x : ℝ) :
      deriv (deriv (fun y => e (g z y))) x =
        (1 / M0) ^ 2 • deriv (deriv (qn z)) (x / M0) := by
    rw [show deriv (fun y => e (g z y)) =
      (fun y => (1 / M0) • deriv (qn z) (y / M0)) from funext (hg1 z)]
    have hd := ((hqder2 z (x / M0)).scomp x (hscale x)).fun_const_smul (1 / M0)
    simpa only [Function.comp_def, smul_smul, ← pow_two] using hd.deriv
  have hmap : Continuous (fun z : Z × ℝ => (z.1, z.2 / M0)) :=
    continuous_fst.prodMk (continuous_snd.div_const M0)
  have hg0c : Continuous (fun z : Z × ℝ => e (g z.1 z.2)) := hq0.comp hmap
  have hg1c : Continuous (fun z : Z × ℝ => deriv (fun y => e (g z.1 y)) z.2) := by
    have hs : Continuous (fun _ : Z × ℝ => (1 / M0 : ℝ)) := continuous_const
    have hv : Continuous (fun z : Z × ℝ => deriv (qn z.1) (z.2 / M0)) := hq1.comp hmap
    exact (hs.smul hv).congr (fun z => (hg1 z.1 z.2).symm)
  have hg2c : Continuous (fun z : Z × ℝ =>
      deriv (deriv (fun y => e (g z.1 y))) z.2) := by
    have hs : Continuous (fun _ : Z × ℝ => (1 / M0 : ℝ) ^ 2) := continuous_const
    have hv : Continuous (fun z : Z × ℝ => deriv (deriv (qn z.1)) (z.2 / M0)) :=
      hq2.comp hmap
    exact (hs.smul hv).congr (fun z => (hg2 z.1 z.2).symm)
  refine ⟨L, hL, g, m, fun z x => phi z x, ?_, ?_, ?_, ?_,
    hmc.div_const M0, div_self hM0.ne', hg0c, hg1c, hg2c,
    ?_, hphic, hphidc, hphiddc, ?_⟩
  · intro z x
    change gn z ((x + L) / M0) = gn z (x / M0)
    have hshift : (x + L) / M0 = x / M0 + curvePeriod := by
      simp only [L, add_div, mul_div_cancel_right₀ _ hM0.ne']
    rw [hshift]
    exact (hnormal z).1 _
  · intro z
    exact (hgn z).comp (contDiff_id.div_const M0).contMDiff
  · intro z x
    rw [curveVelocity_comp ((hgn z).mdifferentiable (by norm_num) _) (hscale x)]
    exact smul_ne_zero hscalePos.ne' ((hnormal z).2.2.1 _)
  · intro z x
    have hs := curveSpeed_comp F (fun y (_ : ℝ) => gn z y) (t := a) (x := x)
      ((hgn z).mdifferentiable (by norm_num) _) (hscale x) hscalePos.le
    change curveSpeed F (fun y (_ : ℝ) => gn z (y / M0)) a x = mean z / M0
    rw [hs, (hnormal z).2.2.2.1]
    change (1 / M0) * mean z = mean z / M0
    ring
  · intro z
    obtain ⟨_hform, hpc, _hpic, _hpzero, hshift, _hishift, hpos⟩ := hphi z
    exact ⟨hpc, fun x => (hpos x).1, hshift⟩
  · intro z x
    have hkappa : L / curvePeriod = M0 := mul_div_cancel_left₀ M0 Real.two_pi_pos.ne'
    change gamma z ((phi z).symm (((L / curvePeriod) * phi z x) / M0)) = gamma z x
    rw [hkappa, mul_div_cancel_left₀ _ hM0.ne', (phi z).symm_apply_apply]

omit [Fintype ι] in
private theorem exists_continuous_periodic_lift
    {P : Type w} [TopologicalSpace P] {L : ℝ} [Fact (0 < L)]
    (f : P → ℝ → W) (hf : Continuous (fun z : P × ℝ => f z.1 z.2))
    (hperiod : ∀ p, Function.Periodic (f p) L) :
    ∃ Q : P → C(AddCircle L, W), Continuous Q ∧
      ∀ p (x : ℝ), Q p (x : AddCircle L) = f p x := by
  let Q : P → C(AddCircle L, W) := fun p => ⟨(hperiod p).lift,
    (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples L)).continuous_iff.mpr
      (hf.comp (continuous_const.prodMk continuous_id))⟩
  have hrep (p : P) (x : ℝ) : Q p (x : AddCircle L) = f p x := by
    change (hperiod p).lift (x : AddCircle L) = f p x
    exact Function.Periodic.lift_coe (hperiod p) x
  refine ⟨Q, ?_, hrep⟩
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hquot : IsOpenQuotientMap (fun z : P × ℝ => (z.1, (z.2 : AddCircle L))) :=
    IsOpenQuotientMap.id.prodMap QuotientAddGroup.isOpenQuotientMap_mk
  apply hquot.continuous_comp_iff.mp
  simpa only [Function.comp_def, Function.uncurry, hrep] using hf

private theorem exists_normalized_local_family
    {L : ℝ} [Fact (0 < L)]
    (F : RicciFlow n M (Icc a b)) (hab : a < b)
    (hcompact : IsCompact (univ : Set M))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p)
    (g : Z → ℝ → M) (hperiod : ∀ z, Function.Periodic (g z) L)
    (hC2 : ∀ z, ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 (g z))
    (himm : ∀ z x, curveVelocity (n := n) (g z) x ≠ 0)
    (Q : Z → ((C(AddCircle L, W) × C(AddCircle L, W)) × C(AddCircle L, W)) × ℝ)
    (hQ : Continuous Q)
    (hjets : ∀ z (x : ℝ), (Q z).1.1.1 (x : AddCircle L) = e (g z x) ∧
      (Q z).1.1.2 (x : AddCircle L) = deriv (fun y => e (g z y)) x ∧
      (Q z).1.2 (x : AddCircle L) = deriv (deriv (fun y => e (g z y))) x)
    (hspeed : ∀ z x, curveSpeed F (fun y _ => g z y) a x = (Q z).2)
    (z0 : Z) (hcenter : (Q z0).2 = 1) :
    ∃ N : Set Z, IsClosed N ∧ z0 ∈ interior N ∧
      ∃ T : ℝ, a < T ∧ T ≤ b ∧ ∃ d : N → ℝ → ℝ → M,
        (∀ z, M63C2ShrinkingCurveOn F (d z) (Icc a T)) ∧
        (∀ z x, d z x a = g z ((L / curvePeriod) * x)) ∧
        Continuous (fun z : (N × ℝ) × Icc a T => e (d z.1.1 z.1.2 z.2)) ∧
        Continuous (fun z : (N × ℝ) × Icc a T =>
          deriv (fun x => e (d z.1.1 x z.2)) z.1.2) ∧
        Continuous (fun z : (N × ℝ) × Icc a T =>
          deriv (deriv (fun x => e (d z.1.1 x z.2))) z.1.2) := by
  classical
  let X := C(AddCircle L, W)
  let J := ((X × X) × X) × ℝ
  let SV := State ((ℤ × Fin 2) × ι)
  let eps : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have heps (j : ℕ) : 0 < eps j := by dsimp only [eps]; positivity
  have heps0 : Tendsto eps atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨A, N, hN, hzN, T, hT, hTcap, hT1, B, u, P, R0,
      hB, _hcenterB, htrace, _hKcompact, hAK, hKband, hKder, hKguard,
      hKspeed, hdecoder, hPne, hPsmooth, _hPnear, hPcover, hR0,
      hcap0, _hqc, _hqxc, hqper, hqzero, hqguard, hqflow⟩ :=
    exists_local_compact_spectral_pool F he hU heU hρ hρe g hperiod hC2 himm Q hQ
      hjets hspeed z0 hcenter
      (show 0 < (b - a) / 2 by linarith only [hab])
      (show (b - a) / 2 < b - a by linarith only [hab]) eps heps heps0
  let K : Set J := Q '' N ∪ ⋃ j, (P j : Set J)
  let I := Σ j : ℕ, {p : J // p ∈ P j}
  let tuple : I → J := fun i => i.2.1
  obtain ⟨p0, hp0⟩ := hPne 0
  let : Nonempty I := ⟨⟨0, p0, hp0⟩⟩
  have hpK (i : I) : tuple i ∈ K := Or.inr (mem_iUnion.mpr ⟨i.1, i.2.2⟩)
  have hzK (z : N) : Q z ∈ K := Or.inl ⟨z, z.2, rfl⟩
  have hAB (p : J) (hp : p ∈ K) : A p ∈ B := hAK ⟨p, hp, rfl⟩
  let q : J → ℝ → ℝ → W := fun p =>
    initialResponseCurve (L := L) hT.le (A p) (u (A p))
  have hzero (p : J) (hp : p ∈ K) (x : ℝ) : q p 0 x = p.1.1.1 (x : AddCircle L) :=
    (hqzero (A p) (hAB p hp) x).trans (congrArg Prod.fst (hdecoder p hp _))
  have hfirst (p : J) (hp : p ∈ K) (x : ℝ) :
      deriv (fun y : ℝ => p.1.1.1 (y : AddCircle L)) x = p.1.1.2 (x : AddCircle L) :=
    (hKder p hp x).1.deriv
  have hsecond (p : J) (hp : p ∈ K) (x : ℝ) :
      deriv (deriv (fun y : ℝ => p.1.1.1 (y : AddCircle L))) x = p.1.2 (x : AddCircle L) := by
    rw [show deriv (fun y : ℝ => p.1.1.1 (y : AddCircle L)) =
      (fun y : ℝ => p.1.1.2 (y : AddCircle L)) from funext (hfirst p hp)]
    exact (hKder p hp x).2.deriv
  have hflow (i : I) := hqflow (A (tuple i)) (hAB _ (hpK i))
    ((hPsmooth i.1 _ i.2.2).2.contDiffAt)
  have hfixed (i : I) (t : ℝ) (ht : t ∈ Icc 0 T) (x : ℝ) :
      q (tuple i) t x = e (ρ (q (tuple i) t x)) := by
    apply (hflow i).2.2.2 _ t ht x
    intro y
    change q (tuple i) 0 y = e (ρ (q (tuple i) 0 y))
    rw [hzero _ (hpK i)]
    exact (hKguard _ (hpK i) y).2.1.symm
  have htime (i : I) : ∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun s => q (tuple i) s x)
      (ambientCurvePrincipal F ρ (a + t) (q (tuple i) t x) (deriv (q (tuple i) t) x) •
        deriv (deriv (q (tuple i) t)) x +
        ambientCurveLower F e ρ (a + t) (q (tuple i) t x) (deriv (q (tuple i) t) x)) t := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using (hflow i).2.2.1
  have hspeed0 (i : I) (x : ℝ) :
      curveSpeed F (fun y _ => ρ (q (tuple i) 0 y)) a x = (tuple i).2 := by
    rw [curveSpeed_congr_slice F
      (d := fun y (_ : ℝ) => ρ ((tuple i).1.1.1 (y : AddCircle L)))
      (fun y => congrArg ρ (hzero _ (hpK i) y))]
    exact hKspeed _ (hpK i) x
  let κ := L / curvePeriod
  have hκ : 0 < κ := div_pos (Fact.out : 0 < L) Real.two_pi_pos
  have hinitial (i : I) (x : ℝ) : m62CurvatureSquared F
      (fun y (_ : ℝ) => ρ (q (tuple i) 0 (κ * y))) a x ≤ R0 := by
    rw [curvatureSquared_congr_slice F
      (d := fun y (_ : ℝ) => ρ ((tuple i).1.1.1 ((κ * y : ℝ) : AddCircle L)))
      (fun y => congrArg ρ (hzero _ (hpK i) (κ * y)))]
    exact hcap0 _ (hpK i) κ hκ x
  obtain ⟨psi, hnormal, _hinitspeed, _hspeedband, delta, hdelta, hdeltaT,
      hdeltab, hdeltaone, R, J1, hR, hJ1, hcap, hjet⟩ :=
    exists_countable_normal_pool_common_slab F hcompact he hU heU hρ hρe
      (Fact.out : 0 < L) hT hT1 (by linarith only [hTcap, hab])
      (fun i => q (tuple i)) (fun i => (hflow i).1)
      (fun i t _ => hqper (A (tuple i)) (hAB _ (hpK i)) t)
      (fun i => hqguard (A (tuple i)) (hAB _ (hpK i))) hfixed htime
      (fun i => (tuple i).2) (fun i => ⟨(hKband _ (hpK i)).1.le, (hKband _ (hpK i)).2.le⟩)
      hspeed0 (show 0 ≤ R0 from (by norm_num : (0 : ℝ) ≤ 1).trans hR0) hinitial
  let cn : I → ℝ → ℝ → M := fun i x t =>
    ρ (q (tuple i) (t - a) (psi i (t - a) (κ * x)))
  have hcn (i : I) : M63SmoothShrinkingCurveOn F (cn i) (Icc a (a + T / 4)) :=
    (hnormal i).2.2.2.2.2.2.1
  have hcnjoint (i : I) : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
      (fun z : ℝ × ℝ => cn i z.1 z.2) (univ ×ˢ Icc a (a + T / 4)) :=
    (hnormal i).2.2.2.2.2.2.2.2
  have haD : a < a + delta := by linarith only [hdelta]
  have hshortS : Icc a (a + delta) ⊆ Icc a (a + T / 4) :=
    Icc_subset_Icc_right (by linarith only [hdeltaT, hdelta])
  have hwideS : Icc a (a + 2 * delta) ⊆ Icc a (a + T / 4) :=
    Icc_subset_Icc_right hdeltaT
  have hds : delta ≤ T / 4 := by linarith only [hdeltaT, hdelta]
  have hdT : delta ≤ T := by linarith only [hds, hT]
  have hsub (t : ℝ) (ht : t ∈ Icc 0 delta) : t ∈ Icc 0 T :=
    ⟨ht.1, ht.2.trans hdT⟩
  have hsubS (t : ℝ) (ht : t ∈ Icc 0 delta) : t ∈ Icc 0 (T / 4) :=
    ⟨ht.1, ht.2.trans hds⟩
  let : Fact (0 < curvePeriod) := ⟨Real.two_pi_pos⟩
  let CP := C(Icc a (a + delta), C(AddCircle curvePeriod, W))
  let Y := (CP × CP) × CP
  have hderivper {f : ℝ → W} (hf : Function.Periodic f curvePeriod) :
      Function.Periodic (deriv f) curvePeriod := by
    intro x
    rw [← deriv_comp_add_const]
    exact congrArg (fun f : ℝ → W => deriv f x) (funext hf)
  have bundle (f : ℝ → ℝ → W)
      (hf : ContinuousOn (Function.uncurry f) (Icc a (a + delta) ×ˢ univ))
      (hp : ∀ t ∈ Icc a (a + delta), Function.Periodic (f t) curvePeriod) :
      ∃ A : CP, ∀ (t : Icc a (a + delta)) (x : ℝ),
        A t (x : AddCircle curvePeriod) = f t x := by
    obtain ⟨A, hA, hrep⟩ := exists_continuous_periodic_lift
      (fun (t : Icc a (a + delta)) x => f t x)
      (hf.comp_continuous (continuous_subtype_val.prodMap continuous_id)
        (fun z => ⟨z.1.2, mem_univ _⟩)) (fun t => hp t t.2)
    exact ⟨⟨A, hA⟩, hrep⟩
  have poolpaths (i : I) : ∃ A0 A1 A2 : CP, ∀ (t : Icc a (a + delta)) (x : ℝ),
      A0 t (x : AddCircle curvePeriod) = e (cn i x t) ∧
      A1 t (x : AddCircle curvePeriod) = deriv (fun y => e (cn i y t)) x ∧
      A2 t (x : AddCircle curvePeriod) = deriv (deriv (fun y => e (cn i y t))) x := by
    let f : ℝ → ℝ → W := fun t x => e (cn i x t)
    have hraw : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => e (cn i z.1 z.2))
        (univ ×ˢ Icc a (a + T / 4)) :=
      (he.comp_contMDiffOn (hcnjoint i)).contDiffOn
    have hswap : ContDiff ℝ ∞ (fun z : ℝ × ℝ => (z.2, z.1)) :=
      contDiff_snd.prodMk contDiff_fst
    have hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc a (a + delta) ×ˢ univ) :=
      hraw.comp (f := fun z : ℝ × ℝ => (z.2, z.1)) hswap.contDiffOn
        (fun z hz => ⟨mem_univ _, hshortS hz.1⟩)
    have hf1 : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => deriv (f z.1) z.2)
        (Icc a (a + delta) ×ˢ univ) :=
      contDiffOn_spatial_deriv_of_uniqueDiffOn (uniqueDiffOn_Icc haD) (by simp) hf
    have hf2 : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => deriv (deriv (f z.1)) z.2)
        (Icc a (a + delta) ×ˢ univ) :=
      contDiffOn_spatial_deriv_of_uniqueDiffOn (q := fun t => deriv (f t))
        (m := ∞) (n := ∞) (uniqueDiffOn_Icc haD) (by simp) hf1
    have hp (t : ℝ) (ht : t ∈ Icc a (a + delta)) : Function.Periodic (f t) curvePeriod :=
      fun x => congrArg e ((hcn i).1.periodic t (hshortS ht) x)
    obtain ⟨A0, h0⟩ := bundle f hf.continuousOn hp
    obtain ⟨A1, h1⟩ := bundle (fun t => deriv (f t)) hf1.continuousOn
      (fun t ht => hderivper (hp t ht))
    obtain ⟨A2, h2⟩ := bundle (fun t => deriv (deriv (f t))) hf2.continuousOn
      (fun t ht => hderivper (hderivper (hp t ht)))
    exact ⟨A0, A1, A2, fun t x => ⟨h0 t x, h1 t x, h2 t x⟩⟩
  choose f0 f1 f2 hfp using poolpaths
  let fp : I → Y := fun i => ((f0 i, f1 i), f2 i)
  let lambda := fun p : (ℤ × Fin 2) × ι => periodicSpectrum L p.1
  let V := fun z : SV => initialResponseTrace lambda z hT.le (u z)
  let inc : C(Icc (0 : ℝ) delta, Icc (0 : ℝ) T) :=
    ⟨fun t => ⟨t, hsub t t.2⟩, continuous_subtype_val.subtype_mk _⟩
  let VP := fun p : J => (V (A p)).comp inc
  let E := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm
  let jet := fun (z : SV) (x : AddCircle L) =>
    (E (vectorPeriodicJet (L := L) 1 0 (by omega) z x),
      E (vectorPeriodicJet (L := L) 1 1 (by omega) z x))
  have hdecode (p : J) (t : Icc (0 : ℝ) delta) (x : ℝ) :
      jet (VP p t) (x : AddCircle L) = (q p t x, deriv (q p t) x) := by
    have hproj : projIcc 0 T hT.le (t : ℝ) = inc t := projIcc_of_mem hT.le (hsub t t.2)
    apply Prod.ext
    · change _ = initialResponseCurve (L := L) hT.le (A p) (u (A p)) t x
      simp only [initialResponseCurve, hproj]
      rfl
    · have hd := (initialResponseCurve_spec (L := L) hT.le (A p) (u (A p))).2.2.2 t x
      rw [hproj] at hd
      exact hd.deriv.symm
  have sequence_limit (z : N) (ii : ℕ → I)
      (hi : Tendsto (fun j => tuple (ii j)) atTop (𝓝 (Q z))) :
      ∃ sigma : ℕ → ℕ, StrictMono sigma ∧ ∃ d : ℝ → ℝ → M,
        M63C2ShrinkingCurveOn F d (Icc a (a + delta)) ∧
        (∀ x, d x a = g z (κ * x)) ∧ ∃ G : Y,
          Tendsto (fun j => fp (ii (sigma j))) atTop (𝓝 G) ∧
          ∀ (t : Icc a (a + delta)) (x : ℝ),
            G.1.1 t (x : AddCircle curvePeriod) = e (d x t) ∧
            G.1.2 t (x : AddCircle curvePeriod) = deriv (fun y => e (d y t)) x ∧
            G.2 t (x : AddCircle curvePeriod) = deriv (deriv (fun y => e (d y t))) x := by
    have hstate := A.continuous.continuousAt.tendsto.comp hi
    have hpath := (htrace.continuousOn.continuousAt (hB.mem_nhds (hAB _ (hzK z)))).tendsto.comp
      hstate
    have hVP : Tendsto (fun j => VP (tuple (ii j))) atTop (𝓝 (VP (Q z))) :=
      (inc.continuous_precomp.tendsto (V (A (Q z)))).comp hpath
    have hlim0 := (continuous_fst.fst.fst.tendsto (Q z)).comp hi
    have hlim1 := (continuous_fst.fst.snd.tendsto (Q z)).comp hi
    have hlim2 := (continuous_fst.snd.tendsto (Q z)).comp hi
    have hinit : ∀ r > 0, ∃ N0 : ℕ, ∀ j ≥ N0, ∀ x : ℝ,
        ‖q (tuple (ii j)) 0 x - (Q z).1.1.1 (x : AddCircle L)‖ < r ∧
        ‖deriv (q (tuple (ii j)) 0) x -
          deriv (fun y : ℝ => (Q z).1.1.1 (y : AddCircle L)) x‖ < r ∧
        ‖deriv (deriv (q (tuple (ii j)) 0)) x -
          deriv (deriv (fun y : ℝ => (Q z).1.1.1 (y : AddCircle L))) x‖ < r := by
      intro r hr
      obtain ⟨N0, hN0⟩ := eventually_atTop.mp
        ((Metric.tendsto_nhds.mp hlim0 r hr).and
          ((Metric.tendsto_nhds.mp hlim1 r hr).and (Metric.tendsto_nhds.mp hlim2 r hr)))
      refine ⟨N0, fun j hj x => ?_⟩
      have heq : q (tuple (ii j)) 0 =
          fun y : ℝ => (tuple (ii j)).1.1.1 (y : AddCircle L) :=
        funext (hzero _ (hpK (ii j)))
      rw [heq, hfirst _ (hpK (ii j)), hfirst _ (hzK z),
        hsecond _ (hpK (ii j)), hsecond _ (hzK z)]
      simpa only [dist_eq_norm] using
        And.intro ((ContinuousMap.dist_apply_le_dist
          (f := (tuple (ii j)).1.1.1) (g := (Q z).1.1.1) (x : AddCircle L)).trans_lt
            (hN0 j hj).1)
          (And.intro ((ContinuousMap.dist_apply_le_dist
            (f := (tuple (ii j)).1.1.2) (g := (Q z).1.1.2) (x : AddCircle L)).trans_lt
              (hN0 j hj).2.1)
            ((ContinuousMap.dist_apply_le_dist
              (f := (tuple (ii j)).1.2) (g := (Q z).1.2) (x : AddCircle L)).trans_lt
                (hN0 j hj).2.2))
    have hf : ContDiff ℝ 2 (fun x : ℝ => (Q z).1.1.1 (x : AddCircle L)) := by
      have heq : (fun x : ℝ => (Q z).1.1.1 (x : AddCircle L)) = fun x => e (g z x) :=
        funext fun x => (hjets z x).1
      rw [heq]
      exact ((he.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp (hC2 z)).contDiff
    have hwide (i : I) : M63SmoothShrinkingCurveOn F (cn i) (Icc a (a + 2 * delta)) :=
      ⟨c2_restrict (hcn i).1 hwideS,
        (hcn i).2.mono (prod_mono Subset.rfl (interior_mono hwideS))⟩
    obtain ⟨sigma, hsigma, d, hd, hd0, _hdspeed, A0, A1, A2, G0, G1, G2,
        hA0, hA1, hA2, hArep, hGrep, _huniform⟩ :=
      exists_spectral_sequence_c2_threeJet_limit F hcompact hdelta hdeltaone hdeltab hR hJ1
        he hU heU hρ hρe (fun j => VP (tuple (ii j))) (VP (Q z)) hVP
        (fun j => q (tuple (ii j)))
        (fun j => (hflow (ii j)).1.mono (prod_mono (Icc_subset_Icc_right hdT) Subset.rfl))
        (fun j t => ((hflow (ii j)).2.1 (inc t)).differentiableAt (by simp))
        (fun j => psi (ii j))
        (fun j => ((hnormal (ii j)).2.2.1.of_le
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)).mono
            (prod_mono (Icc_subset_Icc_right hds) Subset.rfl))
        (fun j t ht => (hnormal (ii j)).2.1 t (hsubS t ht))
        (fun j => (hnormal (ii j)).1)
        (fun j t ht => (hnormal (ii j)).2.2.2.2.1 t (hsubS t ht))
        (fun j t ht x => ((hnormal (ii j)).2.2.2.1 t
          (hsubS t (Ioo_subset_Icc_self ht)) x).hasDerivAt
            (Icc_mem_nhds ht.1 (ht.2.trans_le hds)))
        (fun j => (tuple (ii j)).2) (Q z).2
        (fun j => ⟨(hKband _ (hpK (ii j))).1.le, (hKband _ (hpK (ii j))).2.le⟩)
        ⟨(hKband _ (hzK z)).1.le, (hKband _ (hzK z)).2.le⟩
        ((continuous_snd.tendsto (Q z)).comp hi) (fun j => hspeed0 (ii j))
        (Q z).1.1.1 hf hinit
        (fun j => hdecode (tuple (ii j)))
        (fun j t => hqguard (A (tuple (ii j))) (hAB _ (hpK (ii j))) t (hsub t t.2))
        (fun j t => hfixed (ii j) t (hsub t t.2))
        (by
          intro t x
          obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
          change (jet (VP (Q z) t) (y : AddCircle L)).1 ∈ U ∧
            mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (jet (VP (Q z) t) (y : AddCircle L)).1
              (jet (VP (Q z) t) (y : AddCircle L)).2 ≠ 0
          erw [hdecode]
          exact hqguard (A (Q z)) (hAB _ (hzK z)) t (hsub t t.2) y)
        (fun x => (congrArg Prod.fst (hdecode (Q z) _ x)).trans (hzero _ (hzK z) x))
        (fun j => hwide (ii j)) (fun j => hcap (ii j)) (fun j => hjet (ii j))
    have heq0 : (fun j => f0 (ii (sigma j))) = A0 := by
      funext j
      apply ContinuousMap.ext
      intro t
      apply ContinuousMap.ext
      intro y
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
      exact (hfp _ t x).1.trans (hArep j t x).1.symm
    have heq1 : (fun j => f1 (ii (sigma j))) = A1 := by
      funext j
      apply ContinuousMap.ext
      intro t
      apply ContinuousMap.ext
      intro y
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
      exact (hfp _ t x).2.1.trans (hArep j t x).2.1.symm
    have heq2 : (fun j => f2 (ii (sigma j))) = A2 := by
      funext j
      apply ContinuousMap.ext
      intro t
      apply ContinuousMap.ext
      intro y
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
      exact (hfp _ t x).2.2.trans (hArep j t x).2.2.symm
    refine ⟨sigma, hsigma, d, hd, ?_, ((G0, G1), G2), ?_, hGrep⟩
    · intro x
      rw [hd0, (hjets z (κ * x)).1, hρe]
    · have h0 : Tendsto (fun j => f0 (ii (sigma j))) atTop (𝓝 G0) := heq0.symm ▸ hA0
      have h1 : Tendsto (fun j => f1 (ii (sigma j))) atTop (𝓝 G1) := heq1.symm ▸ hA1
      have h2 : Tendsto (fun j => f2 (ii (sigma j))) atTop (𝓝 G2) := heq2.symm ▸ hA2
      exact (h0.prodMk_nhds h1).prodMk_nhds h2
  have members (z : N) : ∃ d : ℝ → ℝ → M,
      M63C2ShrinkingCurveOn F d (Icc a (a + delta)) ∧
      (∀ x, d x a = g z (κ * x)) ∧ ∃ G : Y,
        (∀ (t : Icc a (a + delta)) (x : ℝ),
          G.1.1 t (x : AddCircle curvePeriod) = e (d x t) ∧
          G.1.2 t (x : AddCircle curvePeriod) = deriv (fun y => e (d y t)) x ∧
          G.2 t (x : AddCircle curvePeriod) = deriv (deriv (fun y => e (d y t))) x) ∧
        ∃ ii : ℕ → I, Tendsto (fun j => tuple (ii j)) atTop (𝓝 (Q z)) ∧
          Tendsto (fun j => fp (ii j)) atTop (𝓝 G) := by
    choose p hp hnear using fun j => hPcover j z z.2
    let ii : ℕ → I := fun j => ⟨j, p j, hp j⟩
    have hi : Tendsto (fun j => tuple (ii j)) atTop (𝓝 (Q z)) := by
      apply Metric.tendsto_nhds.mpr
      intro r hr
      filter_upwards [heps0.eventually (gt_mem_nhds hr)] with j hj
      exact (hnear j).trans hj
    obtain ⟨sigma, hsigma, d, hd, hd0, G, hG, hrep⟩ := sequence_limit z ii hi
    exact ⟨d, hd, hd0, G, hrep, fun j => ii (sigma j), hi.comp hsigma.tendsto_atTop, hG⟩
  choose d hd hd0 G hGrep happrox using members
  have hsubseq (z : N) (ii : ℕ → I)
      (hi : Tendsto (fun j => tuple (ii j)) atTop (𝓝 (Q z))) :
      ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
        Tendsto (fun j => fp (ii (sigma j))) atTop (𝓝 (G z)) := by
    obtain ⟨sigma, hsigma, d', hd', hd0', G', hG', hrep'⟩ := sequence_limit z ii hi
    have heq := c2ShrinkingCurve_unique_closed F hcompact hd' (hd z)
      (fun x => (hd0' x).trans (hd0 z x).symm)
    have hslice (t : Icc a (a + delta)) :
        (fun x => e (d' x t)) = fun x => e (d z x t) :=
      funext fun x => congrArg e (heq t t.2 x)
    have hGeq : G' = G z := by
      apply Prod.ext
      · apply Prod.ext
        · ext t y
          obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
          rw [(hrep' t x).1, (hGrep z t x).1, heq t t.2 x]
        · ext t y
          obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
          rw [(hrep' t x).2.1, (hGrep z t x).2.1, hslice]
      · ext t y
        obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
        rw [(hrep' t x).2.2, (hGrep z t x).2.2, hslice]
    exact ⟨sigma, hsigma, hGeq ▸ hG'⟩
  have hGc : Continuous G := continuous_of_approximating_pool_subsequences
    (fun z : N => Q z) (hQ.comp continuous_subtype_val) tuple fp G happrox hsubseq
  have evalpath (A : N → CP) (hA : Continuous A) :
      Continuous (fun z : (N × ℝ) × Icc a (a + delta) =>
        A z.1.1 z.2 (z.1.2 : AddCircle curvePeriod)) :=
    ((hA.comp continuous_fst.fst).eval continuous_snd).eval
      ((AddCircle.continuous_mk' curvePeriod).comp continuous_fst.snd)
  exact ⟨N, hN, hzN, a + delta, haD, (by linarith only [hdeltab, hdelta]), d, hd, hd0,
    (evalpath _ hGc.fst.fst).congr (fun z => (hGrep z.1.1 z.2 z.1.2).1),
    (evalpath _ hGc.fst.snd).congr (fun z => (hGrep z.1.1 z.2 z.1.2).2.1),
    (evalpath _ hGc.snd).congr (fun z => (hGrep z.1.1 z.2 z.1.2).2.2)⟩

theorem exists_local_metric_c2_curve_family
    (F : RicciFlow n M (Icc a b)) (hab : a < b)
    (hcompact : IsCompact (univ : Set M))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p)
    (gamma : Z → ℝ → M)
    (hperiod : ∀ z, Function.Periodic (gamma z) curvePeriod)
    (hC2 : ∀ z, ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 (gamma z))
    (himm : ∀ z x, curveVelocity (n := n) (gamma z) x ≠ 0)
    (hzero : Continuous (fun p : Z × ℝ => e (gamma p.1 p.2)))
    (hfirst : Continuous (fun p : Z × ℝ =>
      deriv (fun y => e (gamma p.1 y)) p.2))
    (hsecond : Continuous (fun p : Z × ℝ =>
      deriv (deriv (fun y => e (gamma p.1 y))) p.2))
    (z0 : Z) :
    ∃ N : Set Z, IsClosed N ∧ z0 ∈ interior N ∧
      ∃ T : ℝ, a < T ∧ T ≤ b ∧ ∃ c : N → ℝ → ℝ → M,
        (∀ z, M63C2ShrinkingCurveOn F (c z) (Icc a T)) ∧
        (∀ z x, c z x a = gamma z x) ∧
        Continuous (fun z : (N × ℝ) × Icc a T => e (c z.1.1 z.1.2 z.2)) ∧
        Continuous (fun z : (N × ℝ) × Icc a T =>
          deriv (fun x => e (c z.1.1 x z.2)) z.1.2) ∧
        Continuous (fun z : (N × ℝ) × Icc a T =>
          deriv (deriv (fun x => e (c z.1.1 x z.2))) z.1.2) := by
  classical
  obtain ⟨L, hL, g, m, phi, hgp, hgC2, hgi, hgspeed, hmc, hmcenter,
      hg0c, hg1c, hg2c, hphi, hphic, hphidc, hphiddc, hrestore⟩ :=
    exists_centered_arclength_data F hab he hU heU hρ hρe gamma
      hperiod hC2 himm hzero hfirst hsecond z0
  let : Fact (0 < L) := ⟨hL⟩
  let f : Z → ℝ → W := fun z x => e (g z x)
  have hf (z : Z) : ContDiff ℝ 2 (f z) :=
    ((he.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp (hgC2 z)).contDiff
  have hfp (z : Z) : Function.Periodic (f z) L := fun x => congrArg e (hgp z x)
  have hfp1 (z : Z) : Function.Periodic (deriv (f z)) L :=
    (hfp z).deriv_of_differentiable ((hf z).differentiable (by norm_num))
  have hfp2 (z : Z) : Function.Periodic (deriv (deriv (f z))) L :=
    (hfp1 z).deriv_of_differentiable (((hf z).deriv' (n := 1)).differentiable (by norm_num))
  obtain ⟨Q0, hQ0, hQ0rep⟩ := exists_continuous_periodic_lift f hg0c hfp
  obtain ⟨Q1, hQ1, hQ1rep⟩ := exists_continuous_periodic_lift
    (fun z => deriv (f z)) hg1c hfp1
  obtain ⟨Q2, hQ2, hQ2rep⟩ := exists_continuous_periodic_lift
    (fun z => deriv (deriv (f z))) hg2c hfp2
  let Q := fun z => (((Q0 z, Q1 z), Q2 z), m z)
  have hQ : Continuous Q := ((hQ0.prodMk hQ1).prodMk hQ2).prodMk hmc
  obtain ⟨N, hN, hzN, T, haT, hTb, d, hd, hd0, hD0, hD1, hD2⟩ :=
    exists_normalized_local_family F hab hcompact he hU heU hρ hρe g hgp hgC2 hgi Q hQ
      (fun z x => ⟨hQ0rep z x, hQ1rep z x, hQ2rep z x⟩) hgspeed z0 hmcenter
  let c : N → ℝ → ℝ → M := fun z x t => d z (phi z x) t
  have hc (z : N) : M63C2ShrinkingCurveOn F (c z) (Icc a T) :=
    c2ShrinkingCurve_fixedLabel_comp F (hd z) (hphi z).1 (hphi z).2.1 (hphi z).2.2
  have hphiD (z : Z) (x : ℝ) : HasDerivAt (phi z) (deriv (phi z) x) x :=
    (((hphi z).1.differentiable (by norm_num)) x).hasDerivAt
  have hphiDD (z : Z) (x : ℝ) :
      HasDerivAt (deriv (phi z)) (deriv (deriv (phi z)) x) x :=
    ((((hphi z).1.deriv' (n := 1)).differentiable (by norm_num)) x).hasDerivAt
  have hreg (z : N) (t : Icc a T) : ContDiff ℝ 2 (fun x => e (d z x t)) :=
    ((he.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp
      ((hd z).spatial_regular t t.2)).contDiff
  have hder (z : N) (t : Icc a T) (x : ℝ) :
      HasDerivAt (fun y => e (d z y t)) (deriv (fun y => e (d z y t)) x) x :=
    ((hreg z t).differentiable (by norm_num) x).hasDerivAt
  have hder2 (z : N) (t : Icc a T) (x : ℝ) : HasDerivAt
      (deriv (fun y => e (d z y t))) (deriv (deriv (fun y => e (d z y t))) x) x :=
    (((hreg z t).deriv' (n := 1)).differentiable (by norm_num) x).hasDerivAt
  have hfirstC (z : N) (t : Icc a T) (x : ℝ) :
      deriv (fun y => e (c z y t)) x =
        deriv (phi z) x • deriv (fun y => e (d z y t)) (phi z x) :=
    ((hder z t (phi z x)).scomp x (hphiD z x)).deriv
  have hsecondC (z : N) (t : Icc a T) (x : ℝ) :
      deriv (deriv (fun y => e (c z y t))) x =
        deriv (phi z) x ^ 2 • deriv (deriv (fun y => e (d z y t))) (phi z x) +
          deriv (deriv (phi z)) x • deriv (fun y => e (d z y t)) (phi z x) := by
    rw [show deriv (fun y => e (c z y t)) =
      (fun y => deriv (phi z) y • deriv (fun x => e (d z x t)) (phi z y))
      from funext (hfirstC z t)]
    have hdiff := (hphiDD z x).fun_smul ((hder2 z t (phi z x)).scomp x (hphiD z x))
    simpa only [Function.comp_def, smul_smul, ← pow_two] using hdiff.deriv
  have harg : Continuous (fun z : (N × ℝ) × Icc a T => ((z.1.1 : Z), z.1.2)) :=
    (continuous_subtype_val.comp continuous_fst.fst).prodMk continuous_fst.snd
  have hlabel : Continuous (fun z : (N × ℝ) × Icc a T => phi z.1.1 z.1.2) :=
    hphic.comp harg
  have hlabel1 : Continuous (fun z : (N × ℝ) × Icc a T => deriv (phi z.1.1) z.1.2) :=
    hphidc.comp harg
  have hlabel2 : Continuous (fun z : (N × ℝ) × Icc a T =>
      deriv (deriv (phi z.1.1)) z.1.2) := hphiddc.comp harg
  let B : (N × ℝ) × Icc a T → (N × ℝ) × Icc a T :=
    fun z => ((z.1.1, phi z.1.1 z.1.2), z.2)
  have hB : Continuous B := (continuous_fst.fst.prodMk hlabel).prodMk continuous_snd
  refine ⟨N, hN, hzN, T, haT, hTb, c, hc, ?_, hD0.comp hB, ?_, ?_⟩
  · intro z x
    exact (hd0 z (phi z x)).trans (hrestore z x)
  · exact (hlabel1.smul (hD1.comp hB)).congr (fun z => (hfirstC z.1.1 z.2 z.1.2).symm)
  · exact (((hlabel1.pow 2).smul (hD2.comp hB)).add
      (hlabel2.smul (hD1.comp hB))).congr (fun z => (hsecondC z.1.1 z.2 z.1.2).symm)

end PoincareConjecture.M63
