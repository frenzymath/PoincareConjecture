import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.Orientation
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.RegularLevel.Band
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.SaddleEnds.ComponentCount

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.PlaneArcs
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

open SaddleLevel Poincare.Geometry.Manifold.RegularLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

theorem connected_top_of_regular_band
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {a b : Real} (hab : a ≤ b)
    (hregular : ∀ q : S2, h q ∈ Icc a b →
      mfderiv (𝓡 2) 𝓘(Real, Real) h q ≠ 0)
    (hbottom : IsConnected (h ⁻¹' {a})) : IsConnected (h ⁻¹' {b}) := by
  obtain ⟨U, _, _, _, hfull, hreg, V, δ, Φ, _, hbottomV, _, hδ,
    hΦ, _, _, hlevels⟩ :=
    exists_sphere_height_level_diffeomorphisms_on_regular_band_of_smooth hh hab hregular
  let := openLevelSetChartedSpace hh U hreg 1 a
  let := openLevelSetChartedSpace hh U hreg 1 b
  obtain ⟨et, het⟩ := hlevels b ⟨hab, le_rfl⟩
  have himage : (fun x => Φ (b - a, x)) '' (h ⁻¹' {a}) = h ⁻¹' {b} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      let xa : openLevelSet h U a :=
        ⟨⟨x, (inter_eq_right.mp (hfull a ⟨le_rfl, hab⟩)) hx⟩, hx⟩
      have hflow : Φ (b - a, x) = openLevelIncl h U b (et xa) := (het xa).symm
      change h (Φ (b - a, x)) = b
      rw [hflow]
      exact (et xa).property
    · intro hy
      let yb : openLevelSet h U b :=
        ⟨⟨y, (inter_eq_right.mp (hfull b ⟨hab, le_rfl⟩)) hy⟩, hy⟩
      let xa := et.symm yb
      refine ⟨openLevelIncl h U a xa, xa.property, ?_⟩
      change Φ (b - a, openLevelIncl h U a xa) = y
      rw [← het xa, show xa = et.symm yb from rfl, et.apply_symm_apply]
      rfl
  rw [← himage]
  apply hbottom.image
  apply hΦ.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
  intro x hx
  refine ⟨⟨by linarith, by linarith⟩, hbottomV ?_⟩
  exact ⟨(inter_eq_right.mp (hfull a ⟨le_rfl, hab⟩)) hx, hx⟩

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

private theorem actual_lower_level_connected_of_one_end
    (hg : g ∈ M.tree.leaves) (d : TerminalSaddleGeometry M P p e)
    (hcount : Nat.card d.ends.LowerCutIndex = 1) :
    IsConnected {q : S2 | inner Real (M.v : E3) (g q) = d.ends.lowerCut} := by
  obtain ⟨i, _⟩ := Nat.card_eq_one_iff_exists.mp hcount
  refine ⟨?_, (actual_slice_preconnected_iff hg d _).mp
    (actual_lower_slice_preconnected_of_one_end hg d hcount)⟩
  let q : sphere (0 : E2) 1 := ⟨EuclideanSpace.single 0 1, by simp⟩
  exact ⟨d.ends.lowerCutCircle i q, d.ends.lowerCutCircle_height i q⟩

theorem actual_lower_band_slice_preconnected_of_one_end
    (hg : g ∈ M.tree.leaves) (d : TerminalSaddleGeometry M P p e)
    (hunique : ∀ q ∈ P.core,
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real (M.v : E3) (g q)) q = 0 → q = p)
    (hcount : Nat.card d.ends.LowerCutIndex = 1)
    {z : Real} (hz : z ∈ Ico d.ends.lowerCut (inner Real (M.v : E3) (g p))) :
    IsPreconnected (d.A z) := by
  let h : S2 → Real := fun q => inner Real (M.v : E3) (g q)
  have hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h :=
    (innerSL Real (M.v : E3)).contMDiff.comp (M.tree.embedding_of_mem_leaves hg).contMDiff
  have hregular (q : S2) (hq : h q ∈ Icc d.ends.lowerCut z) :
      mfderiv (𝓡 2) 𝓘(Real, Real) h q ≠ 0 := by
    intro hcrit
    have hqcore : q ∈ P.core := d.ends.physical_middle_band_subset_core
      ⟨hq.1, by
        have hu := d.upperCut_eq
        have he := d.eta_pos
        dsimp [h] at hq
        linarith [hz.2, hq.2]⟩
    have hqp := hunique q hqcore hcrit
    subst q
    exact hz.2.not_ge hq.2
  apply (actual_slice_preconnected_iff hg d z).mpr
  exact (connected_top_of_regular_band hh hz.1 hregular
    (actual_lower_level_connected_of_one_end hg d hcount)).isPreconnected

theorem actual_negative_slices_preconnected_of_one_end
    (hg : g ∈ M.tree.leaves) (d : TerminalSaddleGeometry M P p e)
    (hunique : ∀ q ∈ P.core,
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real (M.v : E3) (g q)) q = 0 → q = p)
    (hcount : Nat.card d.ends.LowerCutIndex = 1)
    {t : Real} (ht : t ∈ Ico (-d.eta) 0) :
    IsPreconnected (d.A (inner Real (M.v : E3) (g p) + t)) := by
  apply actual_lower_band_slice_preconnected_of_one_end hg d hunique hcount
  rw [d.lowerCut_eq]
  constructor <;> linarith [ht.1, ht.2]

theorem one_lower_end_independent_of_terminal_geometry
    (hg : g ∈ M.tree.leaves) (d d' : TerminalSaddleGeometry M P p e)
    (hunique : ∀ q ∈ P.core,
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real (M.v : E3) (g q)) q = 0 → q = p)
    (hcount : Nat.card d.ends.LowerCutIndex = 1) :
    Nat.card d'.ends.LowerCutIndex = 1 := by
  let h : S2 → Real := fun q => inner Real (M.v : E3) (g q)
  have hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h :=
    (innerSL Real (M.v : E3)).contMDiff.comp (M.tree.embedding_of_mem_leaves hg).contMDiff
  have hlow (D : TerminalSaddleGeometry M P p e) : D.ends.lowerCut < h p := by
    rw [D.lowerCut_eq]
    dsimp [h]
    linarith [D.eta_pos]
  have hregular (D : TerminalSaddleGeometry M P p e) {b : Real} (hb : b < h p)
      (q : S2) (hq : h q ∈ Icc D.ends.lowerCut b) :
      mfderiv (𝓡 2) 𝓘(Real, Real) h q ≠ 0 := by
    intro hc
    have hqcore : q ∈ P.core := D.ends.physical_middle_band_subset_core
      ⟨hq.1, by
        rw [D.upperCut_eq]
        change h q ≤ h p + D.eta
        linarith [hq.2, D.eta_pos]⟩
    have hqp := hunique q hqcore hc
    subst q
    exact hb.not_ge hq.2
  apply d'.ends.card_lowerCutIndex_eq_one_of_isConnected
  have hbottom := actual_lower_level_connected_of_one_end hg d hcount
  rcases le_total d.ends.lowerCut d'.ends.lowerCut with hle | hle
  · exact connected_top_of_regular_band hh hle (hregular d (hlow d')) hbottom
  · have hnegregular (q : S2) (hq : -h q ∈ Icc (-d.ends.lowerCut) (-d'.ends.lowerCut)) :
        mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => -h q) q ≠ 0 := by
      change mfderiv (𝓡 2) 𝓘(Real, Real) (-h) q ≠ 0
      rw [mfderiv_neg]
      exact neg_ne_zero.mpr (hregular d' (hlow d) q ⟨by linarith [hq.2], by linarith [hq.1]⟩)
    have hn := connected_top_of_regular_band hh.neg (neg_le_neg hle) hnegregular
      (show IsConnected ((fun q => -h q) ⁻¹' {-d.ends.lowerCut}) by
        simpa only [preimage, mem_singleton_iff, neg_inj] using hbottom)
    simpa only [preimage, mem_singleton_iff, neg_inj] using hn

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

end

end M38Schoenflies
