import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.AnnularTubeSmoothing
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Directional.Ascent
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Directional.PrescribedSlab

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric

private theorem tube_scale_hessian_mul_radius_le {r δ : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hδ : 0 < δ) (hδquarter : δ ≤ 1 / 4) :
    (4 / (3 * (r / 2 - δ * r / 1024)) + r + δ / 8) * r ≤ 5 := by
  have hT : δ * r / 1024 ≤ r / 64 := by
    nlinarith [mul_le_mul_of_nonneg_right hδquarter hr.le]
  have hden : 0 < 3 * (r / 2 - δ * r / 1024) := by linarith
  have hfirst : 4 / (3 * (r / 2 - δ * r / 1024)) * r ≤ 3 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).mpr
    linarith
  have hsq : r ^ 2 ≤ 1 := by nlinarith
  have hη : δ / 8 * r ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_right hδquarter hr.le]
  nlinarith only [hfirst, hsq, hη]

private theorem tube_scale_losses {r δ : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hδ : 0 < δ) (hδquarter : δ ≤ 1 / 4) :
    let T := δ * r / 1024
    let ε := δ ^ 2 * r / 1048576
    let H := 4 / (3 * (r / 2 - T)) + r + δ / 8
    ε < r / 8 ∧ 2 * ε / T + H * T / 2 < 1 - δ / 8 ∧
      (1 - δ) * (1 + δ / 8) ≤ 1 - δ / 8 - 2 * ε / T - H * T / 2 := by
  let T := δ * r / 1024
  let ε := δ ^ 2 * r / 1048576
  let H := 4 / (3 * (r / 2 - T)) + r + δ / 8
  have hH : H * r ≤ 5 := tube_scale_hessian_mul_radius_le hr hr1 hδ hδquarter
  have herror : 2 * ε / T = δ / 512 := by
    dsimp only [ε, T]
    field_simp
    ring
  have hHT : H * T / 2 ≤ 5 * δ / 2048 := by
    have h := mul_le_mul_of_nonneg_right hH hδ.le
    dsimp only [T]
    nlinarith only [h]
  have hloss : 2 * ε / T + H * T / 2 ≤ 9 * δ / 2048 := by
    rw [herror]
    linarith
  have hε : ε < r / 8 := by
    have hsq : δ ^ 2 ≤ 1 / 16 := by nlinarith
    have h := mul_le_mul_of_nonneg_right hsq hr.le
    dsimp only [ε]
    nlinarith only [h, hr]
  exact ⟨hε, by change 2 * ε / T + H * T / 2 < _; linarith,
    by change (1 - δ) * (1 + δ / 8) ≤ 1 - δ / 8 - 2 * ε / T - H * T / 2
       nlinarith [sq_nonneg δ]⟩

theorem exists_proper_regular_slab_with_near_unit_gradient_and_value_tube_constraints
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hc : MetricComplete g)
    (hsec : ∀ x : M, ∀ v w : TangentSpace (𝓡 n) x,
      -1 ≤ D.sectionalCurvature x v w)
    (p : M) {ι : Type*} [Finite ι] (f h : ι → M → ℝ)
    {U : Set M} (hU : IsOpen U)
    (hf : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f i))
    (hh : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (h i))
    {δold C q : ℝ} (hδold : 0 ≤ δold) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hpair : ∀ i x, x ∈ U →
      g.tangentNorm x (D.gradient (f i) x) ≤ 1 ∧
      g.tangentNorm x (D.gradient (h i) x) ≤ 1 ∧
      g.inner x (D.gradient (f i) x) (D.gradient (h i) x) ≤ -1 + 2 * δold)
    (hhess : ∀ i x, x ∈ U → ∀ v : TangentSpace (𝓡 n) x,
      D.hessian (f i) x v v ≤ C * g.inner x v v ∧
      D.hessian (h i) x v v ≤ C * g.inner x v v)
    {r δ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hδ : 0 < δ) (hδquarter : δ ≤ 1 / 4)
    (hball : ∀ x, g.edist p x ≤ ENNReal.ofReal (4 * r) → x ∈ U)
    (hascent : ∀ y : M, r / 2 < (g.edist p y).toReal →
      (g.edist p y).toReal < 3 * r → ∀ s : ℝ, 0 < s →
        ∃ z : M, (g.edist y z).toReal < s ∧
          (1 - δ / 8) * (g.edist y z).toReal <
            (g.edist p z).toReal - (g.edist p y).toReal) :
    let τ := 1 / (1 + δ / 8)
    let ε := δ ^ 2 * r / 1048576
    let I := Ioo (τ * (9 * r / 8)) (τ * (15 * r / 8))
    ∃ u : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u ∧
      IsProperMap (I.restrictPreimage u) ∧
      (∀ x : M, u x ∈ I → mfderiv (𝓡 n) 𝓘(ℝ, ℝ) u x ≠ 0) ∧
      (∀ x : M, u x ∈ I →
        r < (g.edist p x).toReal ∧ (g.edist p x).toReal < 2 * r) ∧
      ∀ x : M, r < (g.edist p x).toReal → (g.edist p x).toReal < 2 * r →
        |u x - τ * (g.edist p x).toReal| ≤ τ * ε ∧
        1 - δ ≤ g.tangentNorm x (D.gradient u x) ∧
        g.tangentNorm x (D.gradient u x) ≤ 1 ∧
        (∀ v : TangentSpace (𝓡 n) x,
          D.hessian u x v v ≤ (5 / r) * g.inner x v v) ∧
        ((∀ i, |f i x - f i p| ≤ q) → ∀ i,
          |g.inner x (D.gradient u x) (D.gradient (f i) x)| ≤
            τ * (4 * Real.sqrt δold + 3 * q / r + 2 * C * r + δ / 8) ∧
          |g.inner x (D.gradient u x) (D.gradient (h i) x)| ≤
            τ * (4 * Real.sqrt δold + 3 * q / r + 2 * C * r + δ / 8)) := by
  let : ConnectedSpace M := { toNonempty := ⟨p⟩ }
  let T := δ * r / 1024
  let ε := δ ^ 2 * r / 1048576
  let η := δ / 8
  let H := 4 / (3 * (r / 2 - T)) + r + η
  let L := 1 - δ / 8 - 2 * ε / T - H * T / 2
  let τ := 1 / (1 + δ / 8)
  have hT : 0 < T := by dsimp only [T]; positivity
  have hTsmall : T ≤ r / 64 := by
    dsimp only [T]
    nlinarith [mul_le_mul_of_nonneg_right hδquarter hr.le]
  have hTr : T < r / 2 := by linarith
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hη : 0 < η := by dsimp only [η]; positivity
  have hH : H * r ≤ 5 := tube_scale_hessian_mul_radius_le hr hr1 hδ hδquarter
  have hHpos : 0 < H := by dsimp only [H]; positivity
  have hHle : H ≤ 5 / r := (le_div_iff₀ hr).mpr hH
  have hden : 0 < 1 + δ / 8 := by positivity
  have hτ : 0 < τ := by dsimp only [τ]; positivity
  have hτle : τ ≤ 1 := by
    dsimp only [τ]
    exact (div_le_one hden).mpr (by linarith)
  have hloss := tube_scale_losses hr hr1 hδ hδquarter
  change ε < r / 8 ∧ 2 * ε / T + H * T / 2 < 1 - δ / 8 ∧
    (1 - δ) * (1 + δ / 8) ≤ L at hloss
  have hlower : 1 - δ ≤ τ * L := by
    dsimp only [τ]
    rw [one_div_mul_eq_div]
    exact (le_div_iff₀ hden).mpr hloss.2.2
  obtain ⟨rho, hrho, hrhobounds⟩ :=
    g.exists_annular_distance_smoothing_with_value_tube_constraints D hc
      (K := 1) zero_le_one hsec p f h hU hf hh hδold hC hpair hhess
      (r := r / 2 - T) (R := 3 * r + T) (R' := 4 * r)
      (by linarith) (by linarith) hball hq hε hη
  have hcoefficient : 4 / (3 * (r / 2 - T)) + 1 * (4 * r) / 4 + η = H := by
    dsimp only [H]; ring
  have hub (x : M) (hx : r / 2 - T < (g.edist p x).toReal)
      (hx' : (g.edist p x).toReal < 3 * r + T) :
      |rho x - (g.edist p x).toReal| ≤ ε ∧
      g.tangentNorm x (D.gradient rho x) ≤ 1 + η ∧
      ∀ v : TangentSpace (𝓡 n) x, D.hessian rho x v v ≤ H * g.inner x v v := by
    have hb := hrhobounds x hx.le hx'.le
    exact ⟨hb.1, hb.2.1, hcoefficient ▸ hb.2.2.1⟩
  have heq : (δ / 8 * T + 2 * ε) / T = δ / 8 + 2 * ε / T := by
    field_simp
  have hsmall : (δ / 8 * T + 2 * ε) / T + H * T / 2 < 1 := by
    rw [heq]
    linarith [hloss.2.1]
  have hgeo (x : M) (hx : r < (g.edist p x).toReal)
      (hx' : (g.edist p x).toReal < 2 * r) :
      ∃ q : M, T ≤ (g.edist x q).toReal ∧
        (g.edist p x).toReal + (g.edist x q).toReal - (g.edist p q).toReal ≤
          δ / 8 * T := by
    obtain ⟨q, hq, he⟩ := g.exists_small_excess_of_annular_distance_ascent hc p
      (r := r) (R := 2 * r) (c := 1 - δ / 8) hT (by linarith)
      (fun y hy hy' => hascent y (by linarith) (by linarith)) x hx.le hx'.le
    refine ⟨q, hq.ge, ?_⟩
    convert he using 1
    ring
  obtain ⟨v, hv, hproper, _, hband, hbounds⟩ :=
    g.exists_proper_regular_slab_of_prescribed_approximation D hc p hrho
      (r₀ := r / 2) (r₁ := r) (R₀ := 2 * r) (R₁ := 3 * r)
      (T := T) (ε := ε) (η := η) (δ := δ / 8 * T) (H := H)
      (a := 9 * r / 8) (b := 15 * r / 8)
      hT (by linarith) (by linarith) (by linarith) (by positivity)
      (by linarith) (by linarith [hloss.1]) (by linarith [hloss.1])
      hsmall hub hgeo
  have hLeq : 1 - (δ / 8 * T + 2 * ε) / T - H * T / 2 = L := by
    rw [heq]
    dsimp only [L]
    ring
  let u := fun x => τ * v x
  have hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u := contMDiff_const.mul hv
  have hgrad (x : M) : D.gradient u x = τ • D.gradient v x := by
    apply (g.inner_isInvertible x).injective
    ext w
    rw [D.inner_gradient, mvfderiv_const_mul]
    simp only [map_smul, smul_apply, smul_eq_mul, D.inner_gradient]
  have hnorm (x : M) :
      g.tangentNorm x (D.gradient u x) = τ * g.tangentNorm x (D.gradient v x) := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    rw [hgrad]
    change ‖τ • D.gradient v x‖ = τ * ‖D.gradient v x‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hτ]
  let I := Ioo (τ * (9 * r / 8)) (τ * (15 * r / 8))
  have hbandu (x : M) (hx : u x ∈ I) :
      r < (g.edist p x).toReal ∧ (g.edist p x).toReal < 2 * r := by
    apply hband x
    simpa only [u, I, mem_Ioo, mul_lt_mul_iff_right₀ hτ] using hx
  have hboundsu (x : M) (hx : r < (g.edist p x).toReal)
      (hx' : (g.edist p x).toReal < 2 * r) :
      |u x - τ * (g.edist p x).toReal| ≤ τ * ε ∧
      1 - δ ≤ g.tangentNorm x (D.gradient u x) ∧
      g.tangentNorm x (D.gradient u x) ≤ 1 ∧
      (∀ w : TangentSpace (𝓡 n) x,
        D.hessian u x w w ≤ (5 / r) * g.inner x w w) ∧
      ((∀ i, |f i x - f i p| ≤ q) → ∀ i,
        |g.inner x (D.gradient u x) (D.gradient (f i) x)| ≤
          τ * (4 * Real.sqrt δold + 3 * q / r + 2 * C * r + δ / 8) ∧
        |g.inner x (D.gradient u x) (D.gradient (h i) x)| ≤
          τ * (4 * Real.sqrt δold + 3 * q / r + 2 * C * r + δ / 8)) := by
    obtain ⟨hlocal, hvalue, hlow, hupp, hhessian⟩ := hbounds x hx hx'
    rw [hLeq] at hlow
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · change |τ * v x - τ * (g.edist p x).toReal| ≤ τ * ε
      rw [← mul_sub, abs_mul, abs_of_pos hτ]
      exact mul_le_mul_of_nonneg_left hvalue hτ.le
    · rw [hnorm]
      exact hlower.trans (mul_le_mul_of_nonneg_left hlow hτ.le)
    · rw [hnorm]
      calc
        _ ≤ τ * (1 + η) := mul_le_mul_of_nonneg_left hupp hτ.le
        _ = 1 := by dsimp only [τ, η]; field_simp
    · intro w
      change D.hessian (fun y => τ * v y) x w w ≤ _
      rw [D.hessian_const_mul]
      have hw : 0 ≤ g.inner x w w := by
        by_cases hw : w = 0
        · simp [hw]
        · exact (g.pos x w hw).le
      calc
        _ ≤ τ * (H * g.inner x w w) :=
          mul_le_mul_of_nonneg_left (hhessian w) hτ.le
        _ = (τ * H) * g.inner x w w := by ring
        _ ≤ (5 / r) * g.inner x w w := mul_le_mul_of_nonneg_right
          ((mul_le_mul_of_nonneg_right hτle hHpos.le).trans (by simpa using hHle)) hw
    · intro hlevel i
      have hvgrad : D.gradient v x = D.gradient rho x := by
        simp only [LeviCivitaData.gradient, Poincare.mvfderiv_eq_of_eventuallyEq hlocal]
      have hcros := (hrhobounds x (by linarith) (by linarith)).2.2.2 hlevel i
      have hqdiv : q / (r / 2 - T) ≤ 3 * q / r := by
        calc
          _ ≤ q / (r / 3) := div_le_div_of_nonneg_left hq (by positivity) (by linarith)
          _ = 3 * q / r := by ring
      have hB : 4 * Real.sqrt δold + q / (r / 2 - T) + C * (4 * r) / 2 + η ≤
          4 * Real.sqrt δold + 3 * q / r + 2 * C * r + δ / 8 := by
        dsimp only [η]
        linarith
      have hcros' := And.intro (hcros.1.trans hB) (hcros.2.trans hB)
      rw [hgrad, hvgrad]
      simp only [map_smul, smul_apply, smul_eq_mul, abs_mul, abs_of_pos hτ]
      exact ⟨mul_le_mul_of_nonneg_left hcros'.1 hτ.le,
        mul_le_mul_of_nonneg_left hcros'.2 hτ.le⟩
  have hproperu : IsProperMap (I.restrictPreimage u) := by
    let target : Ioo (9 * r / 8) (15 * r / 8) ≃ₜ I :=
      (Homeomorph.mulLeft₀ τ hτ.ne').subtype (fun x => by
        change x ∈ Ioo (9 * r / 8) (15 * r / 8) ↔
          τ * x ∈ Ioo (τ * (9 * r / 8)) (τ * (15 * r / 8))
        simp only [mem_Ioo, mul_lt_mul_iff_right₀ hτ])
    let source : (u ⁻¹' I) ≃ₜ (v ⁻¹' Ioo (9 * r / 8) (15 * r / 8)) :=
      (Homeomorph.refl M).subtype (fun x => by
        change τ * v x ∈ Ioo (τ * (9 * r / 8)) (τ * (15 * r / 8)) ↔
          v x ∈ Ioo (9 * r / 8) (15 * r / 8)
        simp only [mem_Ioo, mul_lt_mul_iff_right₀ hτ])
    exact (target.isProperMap.comp hproper).comp source.isProperMap
  refine ⟨u, hu, hproperu, ?_, hbandu, hboundsu⟩
  intro x hx
  apply (g.tangentNorm_gradient_pos_iff u x).mp
  exact (by linarith : 0 < 1 - δ).trans_le
    (hboundsu x (hbandu x hx).1 (hbandu x hx).2).2.1

end PoincareConjecture.RiemannianMetric
