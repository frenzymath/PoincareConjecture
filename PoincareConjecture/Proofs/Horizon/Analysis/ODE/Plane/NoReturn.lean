import PoincareConjecture.Proofs.Horizon.Analysis.ODE.LocalFlow.FlowBox.Connector
import PoincareConjecture.Proofs.Horizon.Analysis.ODE.LocalFlow.FlowBox.FirstReturn
import PoincareConjecture.Proofs.Horizon.Analysis.ODE.LocalFlow.FlowBox.SupportedChange
import PoincareConjecture.Proofs.Horizon.Analysis.ODE.Plane.NoPeriodicOrbit

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped ContDiff Topology

namespace Poincare.ODE.Plane

open Poincare.ODE.LocalFlow

theorem not_isBounded_global_integralCurve
    {V : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hV : ContDiff ℝ ∞ V) (hne : ∀ x, V x ≠ 0)
    {γ : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hγ : ∀ t, HasDerivAt γ (V (γ t)) t) :
    ¬ Bornology.IsBounded (γ '' Ici 0) := by
  intro hbounded
  obtain ⟨e, ε, hε, hbox, hp, he, hi, hflow, _⟩ :=
    exists_flowBox_transverse_returns hV hne (fun t _ => hγ t) hbounded
  let r := ε / 2
  have hr : 0 < r := half_pos hε
  have hrε : r < ε := half_lt_self hε
  have hreturns := flowBox_transverse_returns_of_clusterPt hV hγ e hflow hr hrε hbox hp
  obtain ⟨a, b, s₁, s₂, R, h, _, hab, hrR, hh, hhε, hs₁, hs₂,
      hrect, heqa, heqb, havoid⟩ :=
    exists_isolated_flowBox_return hV hγ e hflow hr hrε hbox hreturns
  let R' := (r + R) / 2
  have hrR' : r < R' := by dsimp [R']; linarith
  have hR'R : R' < R := by dsimp [R']; linarith
  have hR' : 0 < R' := hr.trans hrR'
  obtain ⟨W, κ, hW, _, hWvert, hWfix, hκ, hκbound, hκlo, hκhi⟩ :=
    exists_vertical_field_connector hr hrR' (half_pos hh)
      (abs_le.mpr hs₁) (abs_le.mpr hs₂)
  let K : Set (ℝ × ℝ) := Icc (-R') R' ×ˢ Icc (-(h / 2)) (h / 2)
  have hKs : K ⊆ e.source := by
    intro z hz
    exact hrect ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩,
      ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩
  have hKo : K ⊆ Ioo (-R) R ×ˢ Ioo (-h) h := by
    intro z hz
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩,
      ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩
  have hv : ∀ z ∈ e.source, fderiv ℝ e z (0, 1) = V (e z) := by
    rintro ⟨s, t⟩ hz
    have hd := (he.contDiffAt (e.open_source.mem_nhds hz)).differentiableAt (by simp)
    exact (hd.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_const t s).prodMk (hasDerivAt_id t))).unique (hflow s t hz)
  obtain ⟨Z, hZ, hZne, hZfix, hZe⟩ :=
    exists_supported_vectorField_change e he hi hV hne hv
      (isCompact_Icc.prod isCompact_Icc) hKs hW
      (fun z hz => by have := congrArg Prod.snd hz; rw [hWvert] at this; norm_num at this)
      (fun z hz => hWfix z (by
        by_contra hn
        push Not at hn
        exact hz ⟨abs_le.mp hn.1.le, abs_le.mp hn.2.le⟩))
  have hZγ (t : ℝ) (ht : t ∈ Icc (a + h) (b - h)) : Z (γ t) = V (γ t) :=
    hZfix _ (fun htK => havoid t ht (image_mono hKo htK))
  have hκsource (u : ℝ) (hu : u ∈ Icc (-h) h) : κ u ∈ e.source := by
    apply hrect
    have hbnd := abs_le.mp (hκbound u).2
    exact ⟨⟨by linarith [hbnd.1], by linarith [hbnd.2]⟩,
      by simpa only [(hκbound u).1] using hu⟩
  let β : ℝ → EuclideanSpace ℝ (Fin 2) := fun t => e (κ (t - b))
  have hβ (t : ℝ) (ht : t ∈ Icc (b - h) (b + h)) :
      HasDerivAt β (Z (β t)) t := by
    have hsrc := hκsource (t - b) ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hd := (he.contDiffAt (e.open_source.mem_nhds hsrc)).differentiableAt (by simp)
    have hc : HasDerivAt (fun u => e (κ u)) (Z (e (κ (t - b)))) (t - b) := by
      rw [hZe _ hsrc]
      exact hd.hasFDerivAt.comp_hasDerivAt _ (hκ _)
    simpa only [β, Function.comp_def, one_smul, id_eq] using
      hc.scomp t ((hasDerivAt_id t).sub_const b)
  have hβγ : β =ᶠ[𝓝 (b - h)] γ := by
    have hnh : Ioo (b - ε) (b - h / 2) ∈ 𝓝 (b - h) :=
      Ioo_mem_nhds (by linarith) (by linarith)
    filter_upwards [hnh] with t ht
    have hu : t - b ∈ Ioo (-ε) ε := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    dsimp only [β]
    rw [hκlo _ (by linarith [ht.2])]
    symm
    simpa only [add_sub_cancel] using heqb (t - b) hu
  let q : ℝ → EuclideanSpace ℝ (Fin 2) := fun t => if t ≤ b - h then γ t else β t
  have hqleft (t : ℝ) (ht : t ≤ b - h) : q =ᶠ[𝓝 t] γ := by
    rcases lt_or_eq_of_le ht with ht | rfl
    · filter_upwards [eventually_lt_nhds ht] with s hs
      exact if_pos hs.le
    · filter_upwards [hβγ] with s hs
      dsimp only [q]
      split_ifs <;> simp_all
  have hqright (t : ℝ) (ht : b - h < t) : q =ᶠ[𝓝 t] β := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact if_neg (not_le.mpr hs)
  have hq : ∀ t ∈ Icc (a + h) (b + h), HasDerivAt q (Z (q t)) t := by
    intro t ht
    by_cases hb : t ≤ b - h
    · have heq := hqleft t hb
      rw [heq.self_of_nhds, hZγ t ⟨ht.1, hb⟩]
      exact (hγ t).congr_of_eventuallyEq heq
    · have hb' := lt_of_not_ge hb
      have heq := hqright t hb'
      rw [heq.self_of_nhds]
      exact (hβ t ⟨hb'.le, ht.2⟩).congr_of_eventuallyEq heq
  have hclosed : q (a + h) = q (b + h) := by
    have hhI : h ∈ Ioo (-ε) ε := ⟨by linarith, by linarith⟩
    rw [show q (a + h) = γ (a + h) from if_pos (by linarith), heqa h hhI]
    rw [show q (b + h) = β (b + h) from if_neg (by linarith)]
    simp only [β, add_sub_cancel_left, hκhi h (by linarith)]
  have hinj := injOn_integralCurve_Icc_of_nonvanishing hZ hZne hq
  have htimes := hinj ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ hclosed
  linarith

end Poincare.ODE.Plane
