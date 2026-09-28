import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Extremum.DiskSublevels
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.RegularLevel.ComponentBand

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function TopologicalSpace
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

open Poincare.Geometry.Manifold.RegularLevel

private abbrev E1 := EuclideanSpace Real (Fin 1)
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : EuclideanSpace Real (Fin 3)) 1
local notation "Iprod" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)

private instance : ChartedSpace (E1 × Real) (S1 × Real) :=
  prodChartedSpace E1 S1 Real Real

theorem isConnected_regular_band_of_connected_bottom
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {a b : Real} (hab : a ≤ b)
    (hregular : ∀ p : S2, h p ∈ Icc a b →
      mfderiv (𝓡 2) 𝓘(Real, Real) h p ≠ 0)
    (hbottom : IsConnected (h ⁻¹' {a})) : IsConnected (h ⁻¹' Icc a b) := by
  obtain ⟨U, _, _, _, hfull, hreg, V, δ, Φ, hV, hbottomV, _, hδ,
    hΦ, _, _, hlevels⟩ :=
    exists_sphere_height_level_diffeomorphisms_on_regular_band_of_smooth hh hab hregular
  let := openLevelSetChartedSpace hh U hreg 1 a
  let B : Set (Real × S2) := Icc (0 : Real) (b - a) ×ˢ (h ⁻¹' {a})
  have hBconn : IsConnected B :=
    (isConnected_Icc (sub_nonneg.mpr hab)).prod hbottom
  have hBsub : B ⊆ Ioo (-δ) (b - a + δ) ×ˢ V := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    refine ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, hbottomV ?_⟩
    exact ⟨(inter_eq_right.mp (hfull a ⟨le_rfl, hab⟩)) hx, hx⟩
  have himage : Φ '' B = h ⁻¹' Icc a b := by
    ext y
    constructor
    · rintro ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
      have hat : a + t ∈ Icc a b := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      let := openLevelSetChartedSpace hh U hreg 1 (a + t)
      obtain ⟨et, het⟩ := hlevels (a + t) hat
      let xa : openLevelSet h U a :=
        ⟨⟨x, (inter_eq_right.mp (hfull a ⟨le_rfl, hab⟩)) hx⟩, hx⟩
      have hflow : Φ (t, x) = openLevelIncl h U (a + t) (et xa) := by
        simpa only [add_sub_cancel_left, openLevelIncl, xa] using (het xa).symm
      change h (Φ (t, x)) ∈ Icc a b
      rw [hflow, show h (openLevelIncl h U (a + t) (et xa)) = a + t from (et xa).property]
      exact hat
    · intro hy
      let := openLevelSetChartedSpace hh U hreg 1 (h y)
      obtain ⟨et, het⟩ := hlevels (h y) hy
      let yt : openLevelSet h U (h y) :=
        ⟨⟨y, (inter_eq_right.mp (hfull (h y) hy)) rfl⟩, rfl⟩
      let xa := et.symm yt
      refine ⟨(h y - a, openLevelIncl h U a xa),
        ⟨⟨by linarith [hy.1], by linarith [hy.2]⟩, xa.property⟩, ?_⟩
      rw [← het xa, show xa = et.symm yt from rfl, et.apply_symm_apply]
      rfl
  rw [← himage]
  exact hBconn.image Φ (hΦ.continuousOn.mono hBsub)

theorem exists_morse_disk_and_annulus_cover
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    (d : OpenPartialHomeomorph E2 S2) (hds : closedBall 0 1 ⊆ d.source)
    {p : S2} (hp : p ∈ d '' closedBall 0 1) {b : Real} (hpb : h p < b)
    (hboundary : ∀ x ∈ sphere (0 : E2) 1, h (d x) = b)
    (hunique : ∀ x ∈ d '' closedBall 0 1,
      mfderiv (𝓡 2) 𝓘(Real, Real) h x = 0 → x = p)
    (habove : ∀ x ∉ d '' closedBall 0 1, b < h x)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (hform : ∀ x ∈ e.source, h (e x) = h p + ‖x‖ ^ 2) :
    ∃ R : Real, 0 < R ∧ h p + R ^ 2 < b ∧
      closedBall (0 : E2) R ⊆ e.source ∧
      ∀ r ∈ Ioc (0 : Real) R,
        ∃ δ : Real, 0 < δ ∧ ∃ F : OpenPartialHomeomorph (S1 × Real) S2,
          F.source = univ ×ˢ Ioo (h p + r ^ 2 - δ) (b + δ) ∧
          ContMDiffOn Iprod (𝓡 2) ∞ F F.source ∧
          ContMDiffOn (𝓡 2) Iprod ∞ F.symm F.target ∧
          (∀ q t, t ∈ Ioo (h p + r ^ 2 - δ) (b + δ) → h (F (q, t)) = t) ∧
          range (fun q : S1 => F (q, h p + r ^ 2)) = e '' sphere (0 : E2) r ∧
          F '' (univ ×ˢ Icc (h p + r ^ 2) b) =
            (d '' closedBall 0 1) \ (e '' ball (0 : E2) r) ∧
          d '' closedBall 0 1 =
            e '' closedBall (0 : E2) r ∪ F '' (univ ×ˢ Icc (h p + r ^ 2) b) := by
  obtain ⟨_, hbounds, _, _⟩ :=
    height_bounds_on_disk_of_unique_critical hh d hds hp hpb hboundary hunique
  obtain ⟨R, hR, hRb, hRs, _, hsublevels⟩ :=
    exists_exact_morse_sublevels_on_compact_disk hh d hds hp hpb hboundary hunique
      e he0 hep hform
  refine ⟨R, hR, hRb, hRs, ?_⟩
  intro r hr
  let a := h p + r ^ 2
  have hpa : h p < a := by dsimp [a]; nlinarith [sq_pos_of_pos hr.1]
  have hab : a < b := by
    have := (sq_le_sq₀ hr.1.le hR.le).mpr hr.2
    dsimp [a]
    linarith
  obtain ⟨hclosed, hopen, hcircle⟩ := hsublevels r hr
  have hbelow {x : S2} (hx : h x ≤ b) : x ∈ d '' closedBall 0 1 := by
    by_contra hxK
    exact (habove x hxK).not_ge hx
  have hlevel : h ⁻¹' {a} = e '' sphere (0 : E2) r := by
    rw [hcircle]
    apply (inter_eq_right.mpr ?_).symm
    intro x hx
    exact hbelow (show h x ≤ b by change h x = a at hx; rw [hx]; exact hab.le)
  have hlevelconn : IsConnected (h ⁻¹' {a}) := by
    rw [hlevel]
    exact (isConnected_sphere (by simp [← Module.finrank_eq_rank, E2]) (0 : E2) hr.1.le).image
      e (e.continuousOn.mono (sphere_subset_closedBall.trans
        ((closedBall_subset_closedBall hr.2).trans hRs)))
  have hregular (x : S2) (hx : h x ∈ Icc a b) :
      mfderiv (𝓡 2) 𝓘(Real, Real) h x ≠ 0 := by
    intro hcrit
    have hxp := hunique x (hbelow hx.2) hcrit
    subst x
    exact hpa.not_ge hx.1
  have hbandconn := isConnected_regular_band_of_connected_bottom hh hab.le hregular hlevelconn
  obtain ⟨q, hq⟩ := hlevelconn.nonempty
  have hqa : h q = a := hq
  obtain ⟨δ, hδ, F, hFs, hF, hFi, hheight, hcenter, hband⟩ :=
    exists_smooth_regular_band_component_of_smooth hh hab hregular q hqa
  rw [hlevelconn.isPreconnected.connectedComponentIn hq, hlevel] at hcenter
  rw [hbandconn.isPreconnected.connectedComponentIn
    (show q ∈ h ⁻¹' Icc a b by rw [mem_preimage, hqa]; exact ⟨le_rfl, hab.le⟩)] at hband
  have hbandset : h ⁻¹' Icc a b = (d '' closedBall 0 1) \ (e '' ball (0 : E2) r) := by
    rw [hopen]
    ext x
    constructor
    · intro hx
      exact ⟨hbelow hx.2, fun hlt => (not_lt_of_ge hx.1) hlt.2⟩
    · rintro ⟨hx, hxnot⟩
      exact ⟨le_of_not_gt (fun hlt => hxnot ⟨hx, hlt⟩), (hbounds x hx).2⟩
  refine ⟨δ, hδ, F, hFs, hF, hFi, hheight, hcenter, hband.trans hbandset, ?_⟩
  rw [hband, hclosed]
  ext x
  constructor
  · intro hx
    by_cases hxa : h x ≤ a
    · exact Or.inl ⟨hx, hxa⟩
    · exact Or.inr ⟨(lt_of_not_ge hxa).le, (hbounds x hx).2⟩
  · rintro (⟨hx, _⟩ | hx)
    · exact hx
    · exact hbelow hx.2

end Poincare.Manifold.Schoenflies
