import PoincareConjecture.Proofs.M63.Mathlib.PeriodicArclengthEstimates
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicFirstJetComposition
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicC2RelabelingStability
import PoincareConjecture.Proofs.M63.Mathlib.SmoothRetractionDifferentials
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.PullbackMetricHessian
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.SmoothUnitSpeedParameter










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι




theorem exists_smooth_constantSpeed_fixedPeriod_C2_approximation
    (F : RicciFlow n M (Icc a b)) {e : M → W}
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e) {U : Set W} (hU : IsOpen U)
    (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p)
    {t : ℝ} (ht : t ∈ Icc a b) {L : ℝ} (hL : 0 < L) {γ : ℝ → M}
    (hγp : Function.Periodic γ L) (hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 γ)
    (himm : ∀ x, curveVelocity (n := n) γ x ≠ 0)
    (hunit : ∀ x, curveSpeed F (fun y _ => γ y) t x = 1)
    {eps : ℝ} (heps : 0 < eps) :
    let c := fun x => e (γ x)
    ∃ r : ℝ → W, ∃ m : ℝ, 0 < m ∧ |m - 1| < eps ∧
      ContDiff ℝ ∞ r ∧ Function.Periodic r L ∧
      (∀ x, r x ∈ U ∧ e (ρ (r x)) = r x) ∧
      (∀ x, mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (r x) (deriv r x) ≠ 0) ∧
      (∀ x, curveSpeed F (fun y _ => ρ (r y)) t x = m) ∧
      ∀ x, ‖r x - c x‖ < eps ∧ ‖deriv r x - deriv c x‖ < eps ∧
        ‖deriv (deriv r) x - deriv (deriv c) x‖ < eps := by
  let c := fun x => e (γ x)
  have hc : ContDiff ℝ 2 c :=
    ((he.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp hγ).contDiff
  have hcp : Function.Periodic c L := hγp.comp e
  have hcU (x : ℝ) : c x ∈ U := heU (mem_range_self (γ x))
  have hP : ContDiffOn ℝ ∞ (e ∘ ρ) U :=
    (smooth_retraction_differentials he hU heU hρ hρe).1
  have hPU : MapsTo (e ∘ ρ) U U := fun z _ => heU (mem_range_self (ρ z))
  have hPP (z : W) (_hz : z ∈ U) : (e ∘ ρ) ((e ∘ ρ) z) = (e ∘ ρ) z := by
    simp only [Function.comp_apply, hρe]
  have hfix (x : ℝ) : (e ∘ ρ) (c x) = c x := by simp only [Function.comp_apply, c, hρe]
  have hvel (d : ℝ → W) (hd : ContDiff ℝ 1 d) (hdU : ∀ x, d x ∈ U) (x : ℝ) :
      curveVelocity (n := n) (fun y => ρ (d y)) x =
        mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (d x) (deriv d x) := by
    change (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (ρ ∘ d) x) 1 = _
    erw [mfderiv_comp x
      ((hρ.contMDiffAt (hU.mem_nhds (hdU x))).mdifferentiableAt (by simp))
      ((hd.contMDiff x).mdifferentiableAt (by norm_num)),
      ContinuousLinearMap.comp_apply, mfderiv_eq_fderiv]
    rfl
  have hcvel (x : ℝ) : mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (c x) (deriv c x) =
      curveVelocity (n := n) γ x := by
    rw [← hvel c (hc.of_le (by norm_num)) hcU x]
    have hid : (fun y => ρ (c y)) = γ := funext fun y => hρe (γ y)
    rw [hid]
  let Q : W × W → ℝ := fun z => (F.metric t).inner (ρ z.1)
    (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2) (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2)
  have hQ : ContDiffOn ℝ ∞ Q (U ×ˢ univ) :=
    (flow_pullback_metric_hessian_contDiffOn F hU hρ
      (f := fun _ => (0 : ℝ)) contMDiff_const).1.comp
        ((contDiffOn_const.prodMk contDiffOn_fst).prodMk contDiffOn_snd)
        (fun _ hz => ⟨⟨ht, hz.1⟩, mem_univ _⟩)
  let O := (U ×ˢ (univ : Set W)) ∩ Q ⁻¹' Ioi 0
  have hO : IsOpen O := hQ.continuousOn.isOpen_inter_preimage
    (hU.prod isOpen_univ) isOpen_Ioi
  let σ := fun z => Real.sqrt (Q z)
  have hσ : ContDiffOn ℝ ∞ σ O :=
    (hQ.mono inter_subset_left).sqrt (fun _ hz => hz.2.ne')
  have hcO (x : ℝ) : (c x, deriv c x) ∈ O := by
    refine ⟨⟨hcU x, mem_univ _⟩, ?_⟩
    change 0 < (F.metric t).inner (ρ (c x))
      (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (c x) (deriv c x))
      (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (c x) (deriv c x))
    rw [hcvel x]
    change 0 < (F.metric t).inner (ρ (e (γ x))) (curveVelocity γ x) (curveVelocity γ x)
    rw [hρe]
    exact (F.metric t).pos _ _ (himm x)
  have hσc : (fun x => σ (c x, deriv c x)) = fun _ => (1 : ℝ) := by
    funext x
    change Real.sqrt ((F.metric t).inner (ρ (c x))
      (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (c x) (deriv c x))
      (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (c x) (deriv c x))) = 1
    rw [hcvel x]
    change Real.sqrt ((F.metric t).inner (ρ (e (γ x)))
      (curveVelocity γ x) (curveVelocity γ x)) = 1
    rw [hρe]
    exact hunit x
  obtain ⟨δ, hδ, hrelabel⟩ := exists_periodic_C2_relabeling_tolerance hL hc hcp heps
  have hden : 0 < 4 * L + 23 := by positivity
  let η := min (1 / 2) (min eps (δ / (4 * L + 23))) / 2
  have hmin : 0 < min (1 / 2) (min eps (δ / (4 * L + 23))) :=
    lt_min (by norm_num) (lt_min heps (div_pos hδ hden))
  have hη : 0 < η := half_pos hmin
  have hηmin : η < min (1 / 2) (min eps (δ / (4 * L + 23))) := half_lt_self hmin
  have hηhalf : η < 1 / 2 := hηmin.trans_le (min_le_left _ _)
  have hηeps : η < eps := hηmin.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hηprod : η * (4 * L + 23) < δ := (lt_div_iff₀ hden).mp
    (hηmin.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  have hηL : 4 * L * η < δ := by nlinarith only [hηprod, hη]
  have hη4 : 4 * η < δ := by nlinarith only [hηprod, hη, mul_pos hL hη]
  have hη18 : 18 * η < δ := by nlinarith only [hηprod, hη, mul_pos hL hη]
  obtain ⟨θ, hθ, hspeednear⟩ := exists_periodic_C2_tolerance_for_firstJet_composition
    hO (hσ.of_le (by simp)) hL hc hcp hcO hη
  let tol := min (δ / 2) (θ / 2)
  have htol : 0 < tol := lt_min (half_pos hδ) (half_pos hθ)
  have htδ : tol < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have htθ : tol < θ := (min_le_right _ _).trans_lt (half_lt_self hθ)
  obtain ⟨h, hh, hhp, hhfix, happ⟩ := exists_periodic_smooth_fixed_C2_approximation
    hU hP hPU hPP hL hc hcp (by rintro _ ⟨x, rfl⟩; exact hcU x) hfix htol
  have hh2 : ContDiff ℝ 2 h := hh.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have happδ (x : ℝ) : ‖h x - c x‖ < δ ∧ ‖deriv h x - deriv c x‖ < δ ∧
      ‖deriv (deriv h) x - deriv (deriv c) x‖ < δ :=
    ⟨(happ x).1.trans htδ, (happ x).2.1.trans htδ, (happ x).2.2.trans htδ⟩
  obtain ⟨hhO, _hσh, hσnear⟩ := hspeednear h hh2 hhp (fun x =>
    ⟨(happ x).1.trans htθ, (happ x).2.1.trans htθ, (happ x).2.2.trans htθ⟩)
  have hhguard (x : ℝ) : mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (h x) (deriv h x) ≠ 0 := by
    intro hz
    have hqpos := (hhO x).2
    change 0 < (F.metric t).inner (ρ (h x))
      (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (h x) (deriv h x))
      (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (h x) (deriv h x)) at hqpos
    simp only [hz, map_zero] at hqpos
    exact lt_irrefl 0 hqpos
  have hγh : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun x => ρ (h x)) :=
    hρ.comp_contMDiff hh.contMDiff (fun x => (hhfix x).1)
  have hhv (x : ℝ) : curveVelocity (n := n) (fun y => ρ (h y)) x =
      mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (h x) (deriv h x) :=
    hvel h (hh.of_le (by simp)) (fun y => (hhfix y).1) x
  have hγhimm (x : ℝ) : curveVelocity (n := n) (fun y => ρ (h y)) x ≠ 0 := by
    rw [hhv]
    exact hhguard x
  let v := curveSpeed F (fun y _ => ρ (h y)) t
  have hv : ContDiff ℝ ∞ v := speed_contDiff_of_smooth F (fun y _ => ρ (h y)) hγh hγhimm
  have hvpos (x : ℝ) : 0 < v x := Real.sqrt_pos.mpr ((F.metric t).pos _ _ (hγhimm x))
  have hvσ : v = fun x => σ (h x, deriv h x) := by
    funext x
    change Real.sqrt ((F.metric t).inner (ρ (h x))
      (curveVelocity (fun y => ρ (h y)) x) (curveVelocity (fun y => ρ (h y)) x)) = _
    rw [hhv]
  have hvp : Function.Periodic v L := by
    rw [hvσ]
    have hdp := hhp.deriv_of_differentiable (hh.differentiable (by simp))
    intro x
    change σ (h (x + L), deriv h (x + L)) = σ (h x, deriv h x)
    rw [hhp x, hdp x]
  have hvnear (x : ℝ) : |v x - 1| < η ∧ |deriv v x| < η := by
    have hnear := hσnear x
    change |(fun y => σ (h y, deriv h y)) x - (fun y => σ (c y, deriv c y)) x| < η ∧
      |deriv (fun y => σ (h y, deriv h y)) x -
        deriv (fun y => σ (c y, deriv c y)) x| < η at hnear
    rw [← hvσ, hσc] at hnear
    simpa only [deriv_const, sub_zero] using hnear
  let m := (∫ x in (0 : ℝ)..L, v x) / L
  obtain ⟨hell, hmnear, phi, _hformula, _hphi, hψ, _hzero, _hshift, hψshift,
      _hd, _hdd, hψd, _hψdd, _hpositive, _hdispl, _hfirst, _hsecond,
      hψdispl, hψfirst, hψsecond⟩ :=
    exists_smooth_periodic_arclength_homeomorph_estimates hL hv hvp hvpos
      hη.le hηhalf.le (fun x => (hvnear x).1.le) (fun x => (hvnear x).2.le)
  have hmpos : 0 < m := div_pos hell hL
  let r := fun x => h (phi.symm x)
  obtain ⟨_hr2, hrp, herrors⟩ := hrelabel h hh2 hhp phi.symm
    (hψ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hψshift happδ
    (fun x => ⟨(hψdispl x).trans_lt hηL, (hψfirst x).trans_lt hη4,
      (hψsecond x).trans_lt hη18⟩)
  have hrderiv (x : ℝ) : deriv r x = (m / v (phi.symm x)) • deriv h (phi.symm x) :=
    ((hh.differentiable (by simp) (phi.symm x)).hasDerivAt.scomp x (hψd x)).deriv
  refine ⟨r, m, hmpos, hmnear.trans_lt hηeps, hh.comp hψ, hrp,
    fun x => hhfix (phi.symm x), ?_, ?_, herrors⟩
  · intro x
    change mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (h (phi.symm x)) (deriv r x) ≠ 0
    rw [hrderiv x, map_smul]
    exact smul_ne_zero (div_pos hmpos (hvpos _)).ne' (hhguard _)
  · intro x
    calc
      curveSpeed F (fun y _ => ρ (r y)) t x = (m / v (phi.symm x)) * v (phi.symm x) :=
        curveSpeed_comp F (fun y _ => ρ (h y))
          (hγh.mdifferentiable (by simp) _) (hψd x) (div_pos hmpos (hvpos _)).le
      _ = m := div_mul_cancel₀ _ (hvpos _).ne'

end PoincareConjecture.M63
