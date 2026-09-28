import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.AmbientClosedCurveFields
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.AmbientManifoldGauge
import PoincareConjecture.Definitions.M63Ramp

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι

theorem ambientCurve_normal_solution_of_labels (F : RicciFlow n M (Icc a b))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p)
    {L T : ℝ} (hT : 0 < T) (hTb : a + T ≤ b) {q : ℝ → ℝ → W}
    (hq : ContDiffOn ℝ ∞ (Function.uncurry q) (Icc 0 T ×ˢ univ))
    (hper : ∀ t ∈ Icc 0 T, Function.Periodic (q t) L)
    (hguard : ∀ t ∈ Icc 0 T, ∀ y, q t y ∈ U ∧
      mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (q t y) (deriv (q t) y) ≠ 0)
    (hfixed : ∀ t ∈ Icc 0 T, ∀ y, q t y = e (ρ (q t y)))
    (htime : ∀ t ∈ Ioo 0 T, ∀ y, HasDerivAt (fun s => q s y)
      (ambientCurvePrincipal F ρ (a + t) (q t y) (deriv (q t) y) •
          deriv (deriv (q t)) y +
        ambientCurveLower F e ρ (a + t) (q t y) (deriv (q t) y)) t)
    {σ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ) (hσpos : ∀ x, 0 < deriv σ x)
    (hσshift : ∀ x, σ (x + curvePeriod) = σ x + L)
    {δ : ℝ} (hδ : 0 < δ) (hδT : δ < T) {ψ : ℝ → ℝ → ℝ}
    (hψzero : ∀ y, ψ 0 y = y)
    (hψjoint : ContDiffOn ℝ ∞ (Function.uncurry ψ) (Icc 0 δ ×ˢ univ))
    (hψperiod : ∀ t ∈ Icc 0 δ, ∀ y, ψ t (y + L) = ψ t y + L)
    (hψpositive : ∀ t ∈ Icc 0 δ, ∀ y, 0 < deriv (ψ t) y)
    (hψode : ∀ t ∈ Icc 0 δ, ∀ y, HasDerivWithinAt (fun s => ψ s y)
      (deriv (fun z => ambientCurvePrincipal F ρ (a + t)
        (q t z) (deriv (q t) z)) (ψ t y) / 2) (Icc 0 δ) t) :
    let c := fun x t => ρ (q (t - a) (ψ (t - a) (σ x)))
    M63SmoothShrinkingCurveOn F c (Icc a (a + δ)) ∧
      (∀ x, c x a = ρ (q 0 (σ x))) ∧
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
        (fun z : ℝ × ℝ => c z.1 z.2) (univ ×ˢ Icc a (a + δ)) := by
  let label := fun x t => ψ (t - a) (σ x)
  let r := fun t x => q (t - a) (label x t)
  let c := fun x t => ρ (r t x)
  let p := fun t y => q (t - a) y
  let Q := fun y t => ρ (p t y)
  have hδb : a + δ ≤ b := by linarith
  have hshift {t : ℝ} (ht : t ∈ Icc a (a + δ)) : t - a ∈ Icc 0 δ := by
    constructor <;> linarith [ht.1, ht.2]
  have hinc : Icc 0 δ ⊆ Icc 0 T := fun _ ht => ⟨ht.1, ht.2.trans hδT.le⟩
  have hqspace (t : ℝ) (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (q t) :=
    contDiffOn_univ.mp (hq.comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun _ _ => ⟨ht, mem_univ _⟩))
  have hψspace (t : ℝ) (ht : t ∈ Icc 0 δ) : ContDiff ℝ ∞ (ψ t) :=
    contDiffOn_univ.mp (hψjoint.comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun _ _ => ⟨ht, mem_univ _⟩))
  have hlabelspace (t : ℝ) (ht : t ∈ Icc a (a + δ)) :
      ContDiff ℝ ∞ (fun x => label x t) := (hψspace _ (hshift ht)).comp hσ
  have hlabelderiv (t : ℝ) (ht : t ∈ Icc a (a + δ)) (x : ℝ) :
      HasDerivAt (fun y => label y t) (deriv (ψ (t - a)) (σ x) * deriv σ x) x :=
    ((hψspace _ (hshift ht)).differentiable (by simp) (σ x)).hasDerivAt.comp x
      ((hσ.differentiable (by simp) x).hasDerivAt)
  have hlabelpos (t : ℝ) (ht : t ∈ Icc a (a + δ)) (x : ℝ) :
      0 < deriv (fun y => label y t) x := by
    rw [(hlabelderiv t ht x).deriv]
    exact mul_pos (hψpositive _ (hshift ht) _) (hσpos x)
  have hrderiv (t : ℝ) (ht : t ∈ Icc a (a + δ)) (x : ℝ) :
      deriv (r t) x = deriv (fun y => label y t) x • deriv (q (t - a)) (label x t) :=
    (((hqspace _ (hinc (hshift ht))).differentiable (by simp) (label x t)).hasDerivAt.scomp
      x ((hlabelspace t ht).differentiable (by simp) x).hasDerivAt).deriv
  have hlabeljoint : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => label z.2 z.1)
      (Icc a (a + δ) ×ˢ univ) :=
    hψjoint.comp ((contDiffOn_fst.sub contDiffOn_const).prodMk
      (hσ.contDiffOn.comp contDiffOn_snd (fun _ _ => mem_univ _)))
      (fun z hz => ⟨hshift hz.1, mem_univ _⟩)
  have hr : ContDiffOn ℝ ∞ (Function.uncurry r) (Icc a (a + δ) ×ˢ univ) :=
    hq.comp ((contDiffOn_fst.sub contDiffOn_const).prodMk hlabeljoint)
      (fun z hz => ⟨hinc (hshift hz.1), mem_univ _⟩)
  have hrguard (t : ℝ) (ht : t ∈ Icc a (a + δ)) (x : ℝ) :
      r t x ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (r t x) (deriv (r t) x) ≠ 0 := by
    refine ⟨(hguard _ (hinc (hshift ht)) _).1, ?_⟩
    rw [hrderiv t ht x, map_smul]
    exact smul_ne_zero (hlabelpos t ht x).ne' (hguard _ (hinc (hshift ht)) _).2
  have hrfixed (t : ℝ) (ht : t ∈ Icc a (a + δ)) (x : ℝ) :
      r t x = e (ρ (r t x)) := hfixed _ (hinc (hshift ht)) _
  obtain ⟨hcjoint, hcspace, hcimm, hcX, hcH⟩ :=
    ambientCurve_closed_fields F he hU heU hρ hρe (by linarith : a < a + δ)
      hδb hr hrguard hrfixed
  have hp : ContDiffOn ℝ ∞ (Function.uncurry p) (Icc a (a + T) ×ˢ univ) :=
    hq.comp ((contDiffOn_fst.sub contDiffOn_const).prodMk contDiffOn_snd)
      (by intro z hz; exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, mem_univ _⟩)
  have hpguard (t : ℝ) (ht : t ∈ Icc a (a + T)) (y : ℝ) :
      p t y ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (p t y) (deriv (p t) y) ≠ 0 :=
    hguard _ ⟨by linarith [ht.1], by linarith [ht.2]⟩ y
  have hpfixed (t : ℝ) (ht : t ∈ Icc a (a + T)) (y : ℝ) :
      p t y = e (ρ (p t y)) := hfixed _ ⟨by linarith [ht.1], by linarith [ht.2]⟩ y
  obtain ⟨hQjoint, hQspace, hQimm, _hQX, _hQH⟩ :=
    ambientCurve_closed_fields F he hU heU hρ hρe (by linarith only [hT] : a < a + T)
      hTb hp hpguard hpfixed
  have hequation (t : ℝ) (ht : t ∈ Ioo a (a + δ)) (x : ℝ) :
      curveVelocity (n := n) (fun s => c x s) t = m62CurvatureVector F c t x := by
    have htδ : t - a ∈ Ioo 0 δ := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have htT : t - a ∈ Ioo 0 T := ⟨htδ.1, htδ.2.trans hδT⟩
    have htQ : t ∈ Ioo a (a + T) := ⟨ht.1, by linarith [ht.2]⟩
    have htδc : t - a ∈ Icc 0 δ := ⟨htδ.1.le, htδ.2.le⟩
    have htTc : t - a ∈ Icc 0 T := ⟨htT.1.le, htT.2.le⟩
    have htQc : t ∈ Icc a (a + T) := ⟨htQ.1.le, htQ.2.le⟩
    have htc : t ∈ Icc a (a + δ) := ⟨ht.1.le, ht.2.le⟩
    have hphysical : a + (t - a) = t := by ring
    have hQat (y : ℝ) : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) (𝓡 n)
        (fun z : ℝ × ℝ => Q z.1 z.2) (y, t) :=
      (hQjoint.contMDiffAt (prod_mem_nhds (univ_mem) (Icc_mem_nhds htQ.1 htQ.2))).mdifferentiableAt
        (by simp)
    have hQtime (y : ℝ) : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) (fun s => Q y s) t :=
      (hQat y).comp t (((show ContDiff ℝ ∞ (fun s : ℝ => (y, s)) from
        contDiff_const.prodMk contDiff_id).contMDiff t).mdifferentiableAt (by simp))
    have hspaceeq : (fun y => e (Q y t)) = q (t - a) :=
      funext fun y => (hfixed _ htTc y).symm
    have htimeeq (y : ℝ) : (fun s => e (Q y s)) =ᶠ[𝓝 t] (fun s => q (s - a) y) := by
      filter_upwards [isOpen_Ioo.mem_nhds htQ] with s hs
      exact (hfixed _ ⟨by linarith [hs.1], by linarith [hs.2]⟩ y).symm
    have hqpde (y : ℝ) : deriv (fun s => e (Q y s)) t =
        ambientCurvePrincipal F ρ t (e (Q y t)) (deriv (fun z => e (Q z t)) y) •
            deriv (deriv (fun z => e (Q z t))) y +
          ambientCurveLower F e ρ t (e (Q y t)) (deriv (fun z => e (Q z t)) y) := by
      rw [(htimeeq y).deriv_eq, hspaceeq, congrFun hspaceeq y]
      simpa only [Function.comp_def, id_eq, one_smul, hphysical] using
        ((htime _ htT y).scomp t ((hasDerivAt_id t).sub_const a)).deriv
    have hgauge := parabolic_gauge_of_ambient_equation F he hU heU hρ hρe Q
      ((hQspace t htQc).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
      (hQtime (label x t)) (hqpde (label x t))
    have hlabel := ambientCurve_labelVelocity_eq F hU hρ t
      ((hqspace _ htTc).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
      (hguard _ htTc) (label x t)
    change deriv (fun z => ambientCurvePrincipal F ρ t
      (q (t - a) z) (deriv (q (t - a)) z)) (label x t) / 2 =
        -(deriv (curveSpeed F Q t) (label x t) / curveSpeed F Q t (label x t) ^ 3)
      at hlabel
    have hode : HasDerivAt (label x)
        (-(deriv (curveSpeed F Q t) (label x t) / curveSpeed F Q t (label x t) ^ 3)) t := by
      have hd : HasDerivAt (label x)
          (deriv (fun z => ambientCurvePrincipal F ρ t
            (q (t - a) z) (deriv (q (t - a)) z)) (label x t) / 2) t := by
        simpa only [Function.comp_def, id_eq, mul_one, hphysical] using
          ((hψode _ htδc (σ x)).hasDerivAt
            (Icc_mem_nhds htδ.1 htδ.2)).comp t ((hasDerivAt_id t).sub_const a)
      rw [hlabel] at hd
      exact hd
    have hQprod : MDifferentiableAt ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) (𝓡 n)
        (fun z : ℝ × ℝ => Q z.1 z.2) (label x t, t) := by
      rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
      exact hQat (label x t)
    exact normal_equation_of_c2_parabolic_gauge F Q label hQprod
      ((hQspace t htQc).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
      (hQimm t htQc) ((hlabelspace t htc).differentiable (by simp))
      (hlabelpos t htc) hgauge hode
  have hcinterior := hcjoint.mono (Set.prod_mono Subset.rfl interior_subset)
  refine ⟨⟨?_, hcinterior⟩, ?_, hcjoint⟩
  · refine ⟨?_, ?_, ?_, hcinterior.of_le (by simp), hcimm,
      hcjoint.continuousOn, hcX, hcH, ?_⟩
    · exact fun _ ht => ⟨ht.1, ht.2.trans hδb⟩
    · intro t ht x
      change ρ (q (t - a) (ψ (t - a) (σ (x + curvePeriod)))) =
        ρ (q (t - a) (ψ (t - a) (σ x)))
      rw [hσshift, hψperiod _ (hshift ht), hper _ (hinc (hshift ht))]
    · exact fun t ht => (hcspace t ht).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    · simpa only [interior_Icc] using hequation
  · intro x
    change ρ (q (a - a) (ψ (a - a) (σ x))) = _
    rw [sub_self, hψzero]

end PoincareConjecture.M63
