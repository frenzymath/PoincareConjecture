import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Comparison.BadAscentStability
import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Comparison.RadialMonotonicity
import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Packing.ScaledConfigurations

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology Poincare.GromovHausdorff

universe u

namespace Poincare.Alexandrov

private theorem exists_radial_shortening
    {X : Type*} [MetricSpace X] {p q : X}
    (γ : ℝ → X) (hγ0 : γ 0 = p) (hγ1 : γ 1 = q)
    (hγdist : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      dist (γ s) (γ t) = |s - t| * dist p q)
    {r : ℝ} (hr : 0 < r) (hrq : r ≤ dist p q) :
    ∃ z : X, dist p z = r ∧ dist p q = dist p z + dist z q := by
  have hpq : 0 < dist p q := hr.trans_le hrq
  have hparameter : r / dist p q ∈ Icc (0 : ℝ) 1 :=
    ⟨(div_pos hr hpq).le, (div_le_one hpq).mpr hrq⟩
  have hleft := hγdist 0 ⟨le_rfl, zero_le_one⟩ _ hparameter
  simp only [hγ0, zero_sub, abs_neg, abs_of_nonneg hparameter.1,
    div_mul_cancel₀ _ hpq.ne'] at hleft
  have hright := hγdist _ hparameter 1 ⟨zero_le_one, le_rfl⟩
  rw [hγ1, abs_of_nonpos (sub_nonpos.mpr hparameter.2), neg_sub] at hright
  refine ⟨γ (r / dist p q), hleft, ?_⟩
  rw [hleft, hright]
  field_simp
  ring

private theorem exists_common_radius_configuration
    {X : Type*} [MetricSpace X] (hX : CurvatureGEnegOne X)
    (hgeo : ∀ x y : X, ∃ γ : ℝ → X, γ 0 = x ∧ γ 1 = y ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        dist (γ s) (γ t) = |s - t| * dist x y)
    {k : ℕ} (p : X) (q : Fin k → X) {r β : ℝ} (hr : 0 < r)
    (hq : ∀ i, r ≤ dist p (q i))
    (hangle : ∀ i l, i ≠ l →
      β < comparisonAngle (dist p (q i)) (dist p (q l)) (dist (q i) (q l))) :
    ∃ z : Fin k → X, (∀ i, dist p (z i) = r) ∧ ∀ i l, i ≠ l →
      β < comparisonAngle (dist p (z i)) (dist p (z l)) (dist (z i) (z l)) := by
  have hshort (i : Fin k) : ∃ z : X,
      dist p z = r ∧ dist p (q i) = dist p z + dist z (q i) := by
    obtain ⟨γ, hγ0, hγ1, hγdist⟩ := hgeo p (q i)
    exact exists_radial_shortening γ hγ0 hγ1 hγdist hr (hq i)
  choose z hrad hbetween using hshort
  refine ⟨z, hrad, ?_⟩
  intro i l hil
  exact (hangle i l hil).trans_le (hX.comparisonAngle_le_of_two_radial_shortenings
    (by rw [hrad]; exact hr) (by rw [hrad]; exact hr) (hbetween i) (hbetween l))

theorem exists_eventually_scaled_angle_configuration_of_bad_ascent
    {X : ℕ → BasedMetricSpaceBundle.{u}}
    (hX : ∀ j, CurvatureGEnegOne (X j).carrier)
    (hgeo : ∀ j, ∀ x y : (X j).carrier,
      ∃ γ : ℝ → (X j).carrier, γ 0 = x ∧ γ 1 = y ∧
        ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          dist (γ s) (γ t) = |s - t| * dist x y)
    (t : ℕ → ℝ) (ht : ∀ j, 0 < t j) (ht0 : Tendsto t atTop (𝓝 0))
    {k : ℕ} (q : ∀ j, Fin k → (X j).carrier)
    (b : Fin k → ℝ) (d : Fin k → Fin k → ℝ)
    (hb : ∀ i, 0 < b i)
    (hqb : ∀ i, Tendsto (fun j => dist (X j).base (q j i)) atTop (𝓝 (b i)))
    (hqd : ∀ i l, Tendsto (fun j => dist (q j i) (q j l)) atTop (𝓝 (d i l)))
    {θ c ε : ℝ} (hθ : 0 < θ) (hθpi : θ < Real.pi / 2)
    (hc : 0 ≤ c) (hcθ : c < Real.cos (2 * θ)) (hε : 0 < ε)
    (hangle : ∀ i l : Fin k, i ≠ l → θ < comparisonAngle (b i) (b l) (d i l))
    (y : ∀ j, (X j).carrier)
    (hy0 : Tendsto (fun j => dist (X j).base (y j)) atTop (𝓝 0))
    (hyfar : ∀ᶠ j in atTop, ε * t j ≤ dist (X j).base (y j))
    (hybad : ∀ᶠ j in atTop,
      ¬ (∀ s : ℝ, 0 < s → ∃ z : (X j).carrier,
        dist (y j) z < s ∧
          c * dist (y j) z < dist (X j).base z - dist (X j).base (y j))) :
    ∃ β : ℝ, θ < β ∧ β < Real.pi / 2 ∧
      ∀ R : ℝ, 0 < R → R < ε →
        ∀ᶠ j in atTop, ∃ w : Fin (k + 1) → (X j).carrier,
          (∀ i, dist (X j).base (w i) = t j * R) ∧
          ∀ i l, i ≠ l → β < comparisonAngle
            (dist (X j).base (w i)) (dist (X j).base (w l)) (dist (w i) (w l)) := by
  classical
  have hcos : ContinuousAt (fun a : ℝ => Real.cos (2 * a)) θ := by fun_prop
  have hpairs : ∀ᶠ β in 𝓝 θ, ∀ i l : Fin k, i ≠ l →
      β < comparisonAngle (b i) (b l) (d i l) := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro l
    by_cases hil : i = l
    · exact Eventually.of_forall (fun _ hne => (hne hil).elim)
    · exact (eventually_lt_nhds (hangle i l hil)).mono (fun _ h _ => h)
  have hmargin : ∀ᶠ β in 𝓝 θ,
      β < Real.pi / 2 ∧ c < Real.cos (2 * β) ∧
        ∀ i l : Fin k, i ≠ l → β < comparisonAngle (b i) (b l) (d i l) :=
    (eventually_lt_nhds hθpi).and ((hcos.eventually_const_lt hcθ).and hpairs)
  have hright : ∀ᶠ β in 𝓝[>] θ, θ < β := self_mem_nhdsWithin
  obtain ⟨β, hθβ, hβpi, hcβ, hβpairs⟩ :=
    (hright.and (hmargin.filter_mono nhdsWithin_le_nhds)).exists
  have hβ : 0 < β := hθ.trans hθβ
  have hypos : ∀ᶠ j in atTop, 0 < dist (X j).base (y j) := by
    filter_upwards [hyfar] with j hj
    exact (mul_pos hε (ht j)).trans_le hj
  have hnew (i : Fin k) : ∀ᶠ j in atTop,
      β < comparisonAngle (dist (X j).base (y j)) (dist (X j).base (q j i))
        (dist (y j) (q j i)) :=
    eventually_comparisonAngle_gt_of_not_local_ascent hX hgeo (fun j => (X j).base)
      y (fun j => q j i) hy0 (hqb i) (hb i) hβ hβpi hc hcβ hypos hybad
  have hold (i l : Fin k) : ∀ᶠ j in atTop, i ≠ l →
      β < comparisonAngle (dist (X j).base (q j i)) (dist (X j).base (q j l))
        (dist (q j i) (q j l)) := by
    by_cases hil : i = l
    · exact Eventually.of_forall (fun _ hne => (hne hil).elim)
    · have hlim := tendsto_comparisonAngle (hqb i) (hqb l) (hqd i l) (hb i) (hb l)
      exact (hlim.eventually_const_lt (hβpairs i l hil)).mono (fun _ h _ => h)
  refine ⟨β, hθβ, hβpi, ?_⟩
  intro R hR hRε
  have hremote (i : Fin k) : ∀ᶠ j in atTop, t j * R ≤ dist (X j).base (q j i) := by
    have htr : Tendsto (fun j => t j * R) atTop (𝓝 0) := by
      simpa only [zero_mul] using ht0.mul_const R
    exact (htr.eventually_lt (hqb i) (hb i)).mono (fun _ h => h.le)
  let v : ∀ j, Fin (k + 1) → (X j).carrier := fun j => Fin.cons (y j) (q j)
  filter_upwards [hyfar, Filter.eventually_all.mpr hremote,
    Filter.eventually_all.mpr hnew,
    Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (hold i))]
    with j hjfar hjremote hjnew hjold
  apply exists_common_radius_configuration (hX j) (hgeo j) (X j).base (v j)
    (mul_pos (ht j) hR)
  · intro i
    refine Fin.cases ?_ (fun i => hjremote i) i
    change t j * R ≤ dist (X j).base (y j)
    nlinarith only [hjfar, ht j, hRε]
  · intro i l
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun l _ => hjnew l) l
      exact fun hne => (hne rfl).elim
    · refine Fin.cases ?_ (fun l hne => hjold i l (fun hil => hne (congrArg Fin.succ hil))) l
      intro _
      simpa only [v, Fin.cons_zero, Fin.cons_succ, comparisonAngle_comm,
        dist_comm (q j i) (y j)] using hjnew i

theorem exists_small_angle_configuration_of_bad_ascent_blowup
    {X Z : ℕ → BasedMetricSpaceBundle.{u}}
    {Y : BasedMetricSpaceBundle.{u}} [ProperSpace Y.carrier]
    (hX : ∀ j, CurvatureGEnegOne (X j).carrier)
    (hgeo : ∀ j, ∀ x y : (X j).carrier,
      ∃ γ : ℝ → (X j).carrier, γ 0 = x ∧ γ 1 = y ∧
        ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          dist (γ s) (γ t) = |s - t| * dist x y)
    (t : ℕ → ℝ) (ht : ∀ j, 0 < t j)
    (ht0 : Tendsto t atTop (𝓝 0))
    (F : ∀ j, (X j).carrier → (Z j).carrier)
    (hFbase : ∀ j, F j (X j).base = (Z j).base)
    (hscale : ∀ j (x y : (X j).carrier),
      dist x y = t j * dist (F j x) (F j y))
    (hconv : PointedGHConvergesUnbounded Z Y)
    {k : ℕ} (q : ∀ j, Fin k → (X j).carrier)
    (b : Fin k → ℝ) (d : Fin k → Fin k → ℝ)
    (hb : ∀ i, 0 < b i)
    (hqb : ∀ i, Tendsto (fun j => dist (X j).base (q j i)) atTop (𝓝 (b i)))
    (hqd : ∀ i l, Tendsto (fun j => dist (q j i) (q j l)) atTop (𝓝 (d i l)))
    {θ c ε : ℝ} (hθ : 0 < θ) (hθpi : θ < Real.pi / 2)
    (hc : 0 ≤ c) (hcθ : c < Real.cos (2 * θ)) (hε : 0 < ε)
    (hangle : ∀ i l : Fin k, i ≠ l → θ < comparisonAngle (b i) (b l) (d i l))
    (y : ∀ j, (X j).carrier)
    (hy0 : Tendsto (fun j => dist (X j).base (y j)) atTop (𝓝 0))
    (hyfar : ∀ᶠ j in atTop, ε * t j ≤ dist (X j).base (y j))
    (hybad : ∀ᶠ j in atTop,
      ¬ (∀ s : ℝ, 0 < s → ∃ z : (X j).carrier,
        dist (y j) z < s ∧
          c * dist (y j) z < dist (X j).base z - dist (X j).base (y j))) :
    ∀ ρ : ℝ, 0 < ρ → ∃ R : ℝ, 0 < R ∧ R < ρ ∧
      ∃ z : Fin (k + 1) → Y.carrier,
        (∀ i, dist Y.base (z i) = R) ∧
        ∀ i l : Fin (k + 1), i ≠ l →
          θ < comparisonAngle (dist Y.base (z i)) (dist Y.base (z l))
            (dist (z i) (z l)) := by
  classical
  obtain ⟨β, hθβ, hβpi, hspheres⟩ :=
    exists_eventually_scaled_angle_configuration_of_bad_ascent hX hgeo t ht ht0
      q b d hb hqb hqd hθ hθpi hc hcθ hε hangle y hy0 hyfar hybad
  obtain ⟨R₀, hR₀, hconfig⟩ :=
    exists_pos_radius_for_scaled_configurations hθ hθβ (hβpi.trans (by linarith [Real.pi_pos]))
  intro ρ hρ
  let R := min ρ (min ε R₀) / 2
  have hR : 0 < R := half_pos (lt_min hρ (lt_min hε hR₀))
  have hRρ : R < ρ := by dsimp [R]; linarith [min_le_left ρ (min ε R₀)]
  have hRε : R < ε := by
    dsimp [R]
    linarith [min_le_right ρ (min ε R₀), min_le_left ε R₀]
  have hRR₀ : R < R₀ := by
    dsimp [R]
    linarith [min_le_right ρ (min ε R₀), min_le_right ε R₀]
  have hsphere := hspheres R hR hRε
  let L : ℝ := 3 * R + 1
  have hL : 0 < L := by dsimp [L]; positivity
  have hRL : R < L := by dsimp [L]; linarith
  obtain ⟨δ, hδ, hpos, hballs⟩ := hconv L hL
  have hroom : ∀ᶠ j in atTop, R < L + δ j := by
    have hlim : Tendsto (fun j => L + δ j) atTop (𝓝 L) := by
      simpa only [add_zero] using hδ.const_add L
    exact hlim.eventually_const_lt hRL
  obtain ⟨φ, hφ, hφgood⟩ := Filter.extraction_of_frequently_atTop ((hsphere.and hroom).frequently)
  choose w hw hwsep using fun j => (hφgood j).1
  let A : ℕ → FiniteDiameterBasedMetricSpace.{u} := fun j =>
    ballModel (Z j) (L + δ j) (hpos j)
  let B : FiniteDiameterBasedMetricSpace.{u} := ballModel Y L hL
  let S := realizationSequenceOfPointedGHConverges A B hballs
  have hscaledrad (j : ℕ) (i : Fin (k + 1)) :
      dist (Z (φ j)).base (F (φ j) (w j i)) = R := by
    apply (mul_left_cancel₀ (ht (φ j)).ne')
    rw [← hFbase (φ j), ← hscale]
    exact hw j i
  let x : ∀ j, Fin (k + 1) → (A (φ j)).carrier := fun j i =>
    ⟨F (φ j) (w j i), by
      change dist (F (φ j) (w j i)) (Z (φ j)).base < L + δ (φ j)
      rw [dist_comm, hscaledrad]
      exact (hφgood j).2⟩
  have hx (j : ℕ) (i : Fin (k + 1)) : dist (A (φ j)).base (x j i) = R :=
    hscaledrad j i
  have hcompact : IsCompact (Metric.closedBall B.base (2 * R)) := by
    apply Subtype.isCompact_iff.mpr
    have heq : Subtype.val '' Metric.closedBall B.base (2 * R) =
        Metric.closedBall Y.base (2 * R) := by
      ext z
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hz
        have hzL : z ∈ Metric.ball Y.base L := by
          change dist z Y.base < L
          have hzd : dist z Y.base ≤ 2 * R := hz
          dsimp [L]
          linarith
        exact ⟨⟨z, hzL⟩, hz, rfl⟩
    rw [heq]
    exact isCompact_closedBall Y.base (2 * R)
  have hseparated : ∀ᶠ j in atTop, ∀ i l : Fin (k + 1), i ≠ l →
      β ≤ comparisonAngle (t (φ j) * dist (A (φ j)).base (x j i))
        (t (φ j) * dist (A (φ j)).base (x j l)) (t (φ j) * dist (x j i) (x j l)) := by
    apply Eventually.of_forall
    intro j i l hil
    change β ≤ comparisonAngle (t (φ j) * dist (Z (φ j)).base (F (φ j) (w j i)))
      (t (φ j) * dist (Z (φ j)).base (F (φ j) (w j l)))
      (t (φ j) * dist (F (φ j) (w j i)) (F (φ j) (w j l)))
    rw [← hFbase (φ j), ← hscale, ← hscale, ← hscale]
    exact (hwsep j i l hil).le
  obtain ⟨z, hz, hzsep⟩ := hconfig (S.comp φ hφ.tendsto_atTop)
    hR hRR₀ (show R < 2 * R by linarith) hcompact x hx (fun j => t (φ j))
    (ht0.comp hφ.tendsto_atTop) (Eventually.of_forall (fun j => (ht (φ j)).ne')) hseparated
  exact ⟨R, hR, hRρ, fun i => (z i).val, hz, hzsep⟩

end Poincare.Alexandrov
