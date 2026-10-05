import PoincareLib.Topology.Manifold.NeckCap.Geometry.AnalyticTools.Positive.PositiveRadialExtension
import PoincareLib.Topology.Manifold.NeckCap.Geometry.Topology.Gluing.Schoenflies.SchoenfliesRadial

/-!
# Extending the supplied Schoenflies radius

The smooth positive local radius supplied by a Schoenflies datum extends
to an actual smooth open radial chart ending at infinity. Three retained
buffers keep the old formula on the full lower overlap. The collar
embedding hypothesis remains explicit; no service or cap caller is
asserted here. This is StandardEnd F, section 8 of
`tasks/M25/gluing-collar/standard-end-f-plan.md`, for Morgan--Tian A.21,
pp. 510-514.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff

namespace PoincareMT.M25.Topology3D.SchoenfliesData

/-- Extend the supplied local Schoenflies radius in the original height
coordinate, retaining its lower buffered formula and both exact radial
chart domains. The inverse is the smooth actual inverse on the stated
open ray. StandardEnd F, section 8, for MT A.21, pp. 510-514. -/
theorem exists_radial_extension
    {κ : UnitTwoSphere × ℝ → E3} {δ : ℝ} (S : SchoenfliesData κ δ)
    (hκ : IsCollarEmbedding κ) (hδ : 0 ≤ δ)
    {c h tl tm tu b : ℝ} (hh : 0 < h) (hlo : δ < tl)
    (hlm : tl < tm) (hmu : tm < tu) (hhi : tu < 1) (hb : c + h * tu < b) :
    ∃ rho : OpenPartialHomeomorph ℝ ℝ,
      rho.source = Ioo (c + h * tl) b ∧ rho.target = Ioi (S.radial tl) ∧
      ContDiffOn ℝ ∞ (rho : ℝ → ℝ) (Ioo (c + h * δ) b) ∧
      ContDiffOn ℝ ∞ rho.symm rho.target ∧
      EqOn (rho : ℝ → ℝ) (fun s => S.radial ((s - c) / h))
        (Icc (c + h * tl) (c + h * tm)) ∧
      StrictMonoOn (rho : ℝ → ℝ) (Ico (c + h * tl) b) ∧
      (∀ s ∈ Ico (c + h * tl) b, 0 < rho s) ∧
      (∀ s ∈ Ico (c + h * tl) b, 0 < deriv (rho : ℝ → ℝ) s) ∧
      Tendsto (rho : ℝ → ℝ) (𝓝[<] b) atTop := by
  let f : ℝ → ℝ := fun s => S.radial ((s - c) / h)
  have hLl : c + h * δ < c + h * tl := by nlinarith
  have hlm' : c + h * tl < c + h * tm := by nlinarith
  have hmu' : c + h * tm < c + h * tu := by nlinarith
  have huU : c + h * tu < c + h := by nlinarith
  have hnormalized (s : ℝ) (hs : s ∈ Ioo (c + h * δ) (c + h)) :
      (s - c) / h ∈ Ioo δ 1 := by
    constructor
    · apply (lt_div_iff₀ hh).mpr
      nlinarith [hs.1]
    · apply (div_lt_iff₀ hh).mpr
      nlinarith [hs.2]
  have hf : ContDiffOn ℝ ∞ f (Ioo (c + h * δ) (c + h)) :=
    (S.contDiffOn_radial hκ hδ).comp
      ((contDiff_id.sub contDiff_const).div_const h).contDiffOn hnormalized
  have hfderiv : ∀ s ∈ Icc (c + h * tl) (c + h * tu), 0 < deriv f s := by
    intro s hs
    have hs' : s ∈ Ioo (c + h * δ) (c + h) :=
      ⟨hLl.trans_le hs.1, hs.2.trans_lt huU⟩
    have ht := hnormalized s hs'
    have hrad := ((S.contDiffOn_radial hκ hδ).contDiffAt
      (isOpen_Ioo.mem_nhds ht)).differentiableAt (by simp)
    have hderiv : HasDerivAt f (deriv S.radial ((s - c) / h) / h) s := by
      simpa only [f, Function.comp_def, id_eq, one_div, div_eq_mul_inv, one_mul] using!
        hrad.hasDerivAt.comp s (((hasDerivAt_id s).sub_const c).div_const h)
    rw [hderiv.deriv]
    exact div_pos (S.deriv_radial_pos hκ hδ ht) hh
  have hnormalize_anchor : (c + h * tl - c) / h = tl := by
    field_simp [hh.ne']
    ring
  have hanchor : f (c + h * tl) = S.radial tl := by
    change S.radial ((c + h * tl - c) / h) = S.radial tl
    rw [hnormalize_anchor]
  have hfpos : 0 < f (c + h * tl) := by
    rw [hanchor]
    exact S.radial_pos tl ⟨hlo.le, (hlm.trans hmu).trans hhi⟩
  obtain ⟨rho, hsource, htarget, hforward, hinverse, heq, hmono, hpos, hderiv, hlim⟩ :=
    Real.exists_positive_radial_extension hLl hlm' hmu' huU hb hf hfderiv hfpos
  rw [hanchor] at htarget
  exact ⟨rho, hsource, htarget, hforward, hinverse, heq, hmono, hpos, hderiv, hlim⟩

end PoincareMT.M25.Topology3D.SchoenfliesData
