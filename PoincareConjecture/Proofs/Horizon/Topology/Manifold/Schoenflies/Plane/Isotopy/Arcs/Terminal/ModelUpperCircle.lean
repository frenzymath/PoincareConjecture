import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.StandardOrientation
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.NestedOrientation
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.UpperCap



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

open SaddleLevel Poincare.Geometry.Manifold.RegularLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
private instance : Fact (Module.finrank Real E2 = 1 + 1) := ⟨by simp⟩

private theorem connected_bottom_of_regular_band
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {a b : Real} (hab : a ≤ b)
    (hregular : ∀ q : S2, h q ∈ Icc a b → mfderiv (𝓡 2) 𝓘(Real, Real) h q ≠ 0)
    (htop : IsConnected (h ⁻¹' {b})) : IsConnected (h ⁻¹' {a}) := by
  obtain ⟨U, _, _, _, hfull, hreg, V, δ, Φ, _, _, _, _, _, _, _, hlevels⟩ :=
    exists_sphere_height_level_diffeomorphisms_on_regular_band_of_smooth hh hab hregular
  let := openLevelSetChartedSpace hh U hreg 1 a
  let := openLevelSetChartedSpace hh U hreg 1 b
  obtain ⟨e, _⟩ := hlevels b ⟨hab, le_rfl⟩
  let : ConnectedSpace ↥(h ⁻¹' {b}) := isConnected_iff_connectedSpace.mp htop
  let j : ↥(h ⁻¹' {b}) → openLevelSet h U b :=
    fun q => ⟨⟨q, (inter_eq_right.mp (hfull b ⟨hab, le_rfl⟩)) q.property⟩, q.property⟩
  have hj : Continuous j := (continuous_subtype_val.subtype_mk _).subtype_mk _
  let k : ↥(h ⁻¹' {b}) → S2 := openLevelIncl h U a ∘ e.symm ∘ j
  have hk : Continuous k :=
    (isEmbedding_openLevelIncl h U a).continuous.comp (e.symm.continuous.comp hj)
  have hrange : range k = h ⁻¹' {a} := by
    ext q
    constructor
    · rintro ⟨x, rfl⟩
      exact (e.symm (j x)).property
    · intro hq
      let qa : openLevelSet h U a :=
        ⟨⟨q, (inter_eq_right.mp (hfull a ⟨le_rfl, hab⟩)) hq⟩, hq⟩
      let qb : ↥(h ⁻¹' {b}) := ⟨openLevelIncl h U b (e qa), (e qa).property⟩
      refine ⟨qb, ?_⟩
      change openLevelIncl h U a (e.symm (j qb)) = q
      have hjqb : j qb = e qa := rfl
      rw [hjqb, e.symm_apply_apply]
      rfl
  rw [← hrange]
  exact isConnected_range hk

private theorem standard_upper_reference_level_connected :
    IsConnected (Saddle.height ⁻¹' {(1 / 2 : Real)}) := by
  let r := Real.sqrt (3 / 4 : Real)
  have hr : 0 < r := Real.sqrt_pos.mpr (by norm_num)
  have hs (q : sphere (0 : E2) r) : (q : E2) ∈ ball (0 : E2) 1 :=
    Saddle.upper_closedBall_subset_domain (sphere_subset_closedBall q.property)
  have hm (q : sphere (0 : E2) r) :
      Saddle.shear.symm (Saddle.upperCap q) ∈ sphere (0 : E3) 1 := by
    have hsurface : Saddle.upperCap q ∈ Saddle.shear '' sphere (0 : E3) 1 := by
      rw [Saddle.shear_image_sphere]
      exact Saddle.upperCap_mem_surface (hs q)
    obtain ⟨y, hy, heq⟩ := hsurface
    rw [← heq, Saddle.shear.symm_apply_apply]
    exact hy
  let γ : sphere (0 : E2) r → S2 :=
    fun q => ⟨Saddle.shear.symm (Saddle.upperCap q), hm q⟩
  have hγ : Continuous γ := by
    apply Continuous.subtype_mk
    apply Saddle.shear.symm.continuous.comp
    exact Saddle.upperCap_contDiffOn.continuousOn.comp_continuous
      continuous_subtype_val hs
  let : ConnectedSpace (sphere (0 : E2) r) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by simp [← Module.finrank_eq_rank, E2]) (0 : E2) hr.le)
  have hheight (q : sphere (0 : E2) r) : Saddle.height (γ q) = 1 / 2 := by
    change Saddle.shear (Saddle.shear.symm (Saddle.upperCap q)) 2 = _
    rw [Saddle.shear.apply_symm_apply]
    exact Saddle.upperCap_boundary_height q.property
  have hcover : range γ = Saddle.height ⁻¹' {(1 / 2 : Real)} := by
    ext q
    constructor
    · rintro ⟨z, rfl⟩
      exact hheight z
    · intro hq
      have hqheight : Saddle.height q = 1 / 2 := hq
      have hsurface : Saddle.polynomial (Saddle.shear q) = 1 := by
        change Saddle.shear q ∈ {y | Saddle.polynomial y = 1}
        rw [← Saddle.shear_image_sphere]
        exact mem_image_of_mem Saddle.shear q.property
      obtain ⟨u, hu, heq⟩ := Saddle.upperCap_image_closedBall.symm ▸
        (show Saddle.shear q ∈ {y | Saddle.polynomial y = 1 ∧ 1 / 2 ≤ y 2} from
          ⟨hsurface, hqheight.ge⟩)
      have hulevel : Saddle.upperCap u 2 = 1 / 2 := by rw [heq]; exact hqheight
      have husq := (Saddle.upperCap_height_eq_iff
        (Saddle.upper_closedBall_subset_domain hu)).mp hulevel
      have hur : u ∈ sphere (0 : E2) r := by
        rw [mem_sphere_zero_iff_norm]
        have hrsq : r ^ 2 = 3 / 4 := Real.sq_sqrt (by norm_num)
        nlinarith [norm_nonneg u]
      refine ⟨⟨u, hur⟩, ?_⟩
      apply Subtype.ext
      change Saddle.shear.symm (Saddle.upperCap u) = q
      rw [heq, Saddle.shear.symm_apply_apply]
  rw [← hcover]
  exact isConnected_range hγ



theorem exists_standard_upper_source_circle
    {a : Real} (ha : -1 < a) (hau : a ≤ 1 / 2) :
    ∃ C : S1 → S2,
      ContMDiff (𝓡 1) (𝓡 2) ∞ C ∧ Injective C ∧
      (∀ q, Injective (mfderiv (𝓡 1) (𝓡 2) C q)) ∧
      range C = Saddle.height ⁻¹' {a} := by
  have hregular (q : S2) (hq : Saddle.height q ∈ Icc a (1 / 2 : Real)) :
      mfderiv (𝓡 2) 𝓘(Real, Real) Saddle.height q ≠ 0 := by
    intro hc
    rcases Saddle.critical_height_values hc with hh | hh | hh <;> linarith [hq.1, hq.2]
  have hconn := connected_bottom_of_regular_band Saddle.height_contMDiff hau
    hregular standard_upper_reference_level_connected
  obtain ⟨q, hq⟩ := hconn.nonempty
  obtain ⟨C, hC, hi, hd, hrange⟩ := exists_smooth_circle_regularLevelComponent
    Saddle.height_contMDiff a (fun q hq => hregular q ⟨hq.ge, hq.trans_le hau⟩) q hq
  refine ⟨C, hC, hi, hd, ?_⟩
  rw [hrange, hconn.isPreconnected.connectedComponentIn hq]


theorem exists_nested_upper_source_circle
    {p : S2} (hp : mfderiv (𝓡 2) 𝓘(Real, Real) Saddle.Nested.height p = 0)
    (hpz : (p : E3) 2 ∈ Ioo (3 / 5 : Real) (5 / 8))
    {a : Real} (hpa : Saddle.Nested.height p < a) (ha : a ≤ (13 / 10 : Real)) :
    ∃ C : S1 → S2,
      ContMDiff (𝓡 1) (𝓡 2) ∞ C ∧ Injective C ∧
      (∀ q, Injective (mfderiv (𝓡 1) (𝓡 2) C q)) ∧
      range C = Saddle.Nested.height ⁻¹' {a} := by
  obtain ⟨p₀, hp₀z, hp₀h, hp₀, _⟩ := Saddle.Nested.exists_unique_critical_point_in_height_band
  have hp₀p : p₀ = p := Saddle.Nested.critical_latitude_unique_in_saddle_interval hp₀ hp
    (Ioo_subset_Icc_self hp₀z) (Ioo_subset_Icc_self hpz)
  have hph : (1 : Real) < Saddle.Nested.height p := hp₀p ▸ hp₀h.1
  have hregular (q : S2) (hq : Saddle.Nested.height q ∈ Icc a (13 / 10 : Real)) :
      mfderiv (𝓡 2) 𝓘(Real, Real) Saddle.Nested.height q ≠ 0 := by
    intro hc
    have hqp := (Saddle.Nested.critical_in_height_band_iff_eq_saddle hp hpz q
      ⟨hph.le.trans (hpa.le.trans hq.1), hq.2⟩).mp hc
    subst q
    exact hpa.not_ge hq.1
  have hconn := connected_bottom_of_regular_band Saddle.Nested.height_contMDiff ha hregular
    Saddle.Nested.isConnected_upper_height_level
  obtain ⟨q, hq⟩ := hconn.nonempty
  obtain ⟨C, hC, hi, hd, hrange⟩ := exists_smooth_circle_regularLevelComponent
    Saddle.Nested.height_contMDiff a (fun q hq => hregular q ⟨hq.ge, hq.trans_le ha⟩) q hq
  refine ⟨C, hC, hi, hd, ?_⟩
  rw [hrange, hconn.isPreconnected.connectedComponentIn hq]

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}



theorem exists_model_upper_source_circles
    (d : TerminalSaddleGeometry M P p e)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    ∃ ε : Real, 0 < ε ∧ ∀ t ∈ Ioc (0 : Real) ε,
      ∃ C : S1 → S2,
        ContMDiff (𝓡 1) (𝓡 2) ∞ C ∧ Injective C ∧
        (∀ q, Injective (mfderiv (𝓡 1) (𝓡 2) C q)) ∧
        range C = {q : S2 | inner Real (M.v : E3) (d.filledModel q) =
          inner Real (M.v : E3) (g p) + t} := by
  let c := inner Real (M.v : E3) (g p)
  rcases d.model_kind with hmodel | hmodel
  · have hcenter := terminal_standard_model_chart_center d hmodel hform
    have hheight : d.model (d.modelChart 0) 2 = -1 := by
      rw [hmodel, hcenter]
      exact Saddle.height_saddlePoint
    have hphysical (q : S2) : inner Real (M.v : E3) (d.filledModel q) =
        c + d.scale * (Saddle.height q + 1) := by
      change inner Real (M.v : E3) (d.transport (d.model q)) = _
      rw [d.transport_height, hheight, hmodel]
      change c + d.scale * (Saddle.height q - -1) = _
      ring
    refine ⟨d.scale / 2, div_pos d.scale_pos (by norm_num), ?_⟩
    intro t ht
    have hs : 0 < t / d.scale := div_pos ht.1 d.scale_pos
    have hsu : t / d.scale ≤ 1 / 2 := (div_le_iff₀ d.scale_pos).mpr (by
      nlinarith [ht.2])
    obtain ⟨C, hC, hi, hd, hcover⟩ := exists_standard_upper_source_circle
      (a := -1 + t / d.scale) (by linarith) (by linarith)
    refine ⟨C, hC, hi, hd, hcover.trans ?_⟩
    ext q
    change Saddle.height q = -1 + t / d.scale ↔
      inner Real (M.v : E3) (d.filledModel q) = c + t
    rw [hphysical]
    have hmul : t / d.scale * d.scale = t := div_mul_cancel₀ t d.scale_pos.ne'
    constructor <;> intro h <;> nlinarith [d.scale_pos]
  · have hp := terminal_model_chart_critical d hform
    rw [hmodel] at hp
    have hpz := terminal_nested_model_chart_latitude d hmodel hform
    have hupper : Saddle.Nested.height (d.modelChart 0) < (13 / 10 : Real) :=
      (Saddle.Nested.saddle_height_lt_fortyone_fortieths hp hpz).trans (by norm_num)
    have hphysical (q : S2) : inner Real (M.v : E3) (d.filledModel q) =
        c + d.scale * (Saddle.Nested.height q - Saddle.Nested.height (d.modelChart 0)) := by
      change inner Real (M.v : E3) (d.transport (d.model q)) = _
      rw [d.transport_height, hmodel]
      rfl
    refine ⟨d.scale * (13 / 10 - Saddle.Nested.height (d.modelChart 0)),
      mul_pos d.scale_pos (sub_pos.mpr hupper), ?_⟩
    intro t ht
    have hs : 0 < t / d.scale := div_pos ht.1 d.scale_pos
    have hsu : t / d.scale ≤ 13 / 10 - Saddle.Nested.height (d.modelChart 0) :=
      (div_le_iff₀ d.scale_pos).mpr (by simpa only [mul_comm] using ht.2)
    obtain ⟨C, hC, hi, hd, hcover⟩ := exists_nested_upper_source_circle hp hpz
      (a := Saddle.Nested.height (d.modelChart 0) + t / d.scale)
      (by linarith) (by linarith)
    refine ⟨C, hC, hi, hd, hcover.trans ?_⟩
    ext q
    change Saddle.Nested.height q = Saddle.Nested.height (d.modelChart 0) + t / d.scale ↔
      inner Real (M.v : E3) (d.filledModel q) = c + t
    rw [hphysical]
    have hmul : t / d.scale * d.scale = t := div_mul_cancel₀ t d.scale_pos.ne'
    constructor <;> intro h <;> nlinarith [d.scale_pos]

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
