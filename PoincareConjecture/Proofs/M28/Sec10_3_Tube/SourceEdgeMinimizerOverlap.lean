import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalFrontierSeed
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalPrefixSign
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalAxialContinuation
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckFrontierDistance
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckFrontierSphere
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicSplicing
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.NeckCollar
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Intrinsic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck

theorem exists_reciprocal_band_of_positive_frontier_contact :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 10000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (N P : EpsilonNeck g), N.epsilon ≤ ε₀ → P.epsilon = N.epsilon →
        ∀ x : M, x ∈ frontier N.carrier →
        x ∈ closure (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹) →
        x ∈ P.central_sphere →
        ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
          ∀ y ∈ P.carrier, ∀ u, u = σ * (P.coordinate_inverse y).2 →
            -N.epsilon⁻¹ < u → u < -(0.07 : ℝ) * N.epsilon⁻¹ →
            y ∈ N.carrier ∧
            (0.9 : ℝ) * N.epsilon⁻¹ -
                (1.1 : ℝ) * (-u - (0.03 : ℝ) * N.epsilon⁻¹) ≤
              (N.coordinate_inverse y).2 ∧
            (N.coordinate_inverse y).2 ≤ (0.99 : ℝ) * N.epsilon⁻¹ -
                (0.9 : ℝ) * (-u - (0.03 : ℝ) * N.epsilon⁻¹) := by
  obtain ⟨ε₁, hε₁, hsmall, hseed⟩ := exists_frontier_axial_seed_threshold_m28.{u}
  obtain ⟨ε₂, hε₂, _, hprefix⟩ :=
    exists_transition_axis_prefix_signed_deriv_bounds_m28.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂,
    (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g N P hε heq x hxfront hx hxP
  obtain ⟨σ, hσ, hband, horder⟩ := hseed N P
    (hε.trans (min_le_left _ _)) heq x hxfront hx hxP
  refine ⟨σ, hσ, ?_⟩
  intro y hyP u hueq heqlo heqhi
  let R := N.epsilon⁻¹
  let q := (P.coordinate_inverse y).1
  let t₀ := σ * (-(0.03 : ℝ) * R)
  let v := -σ
  let δ := (0.04 : ℝ) * R
  let L := -u - (0.03 : ℝ) * R
  let s₀ := (N.coordinate_inverse (P.coordinate_map (q, t₀))).2
  have hR : 0 < R := inv_pos.mpr N.epsilon_pos
  have hu : -R < u ∧ u < -(0.07 : ℝ) * R := by
    simpa only [R] using ⟨heqlo, heqhi⟩
  have hL : (0.04 : ℝ) * R < L ∧ L < (0.97 : ℝ) * R := by
    dsimp only [L]
    constructor <;> linarith [hu.1, hu.2]
  have hLpos : 0 < L := (mul_pos (by norm_num) hR).trans hL.1
  have hδ : 0 < δ := mul_pos (by norm_num) hR
  have hδL : δ ≤ L := by
    dsimp only [δ]
    linarith [hL.1]
  have hv : v = 1 ∨ v = -1 := by
    dsimp only [v]
    rcases hσ with rfl | rfl <;> norm_num
  have hcoord (s : ℝ) : t₀ + v * s = σ * (-(0.03 : ℝ) * R - s) := by
    dsimp only [t₀, v]
    ring
  have hdom (s : ℝ) (hs : s ∈ Icc 0 L) :
      t₀ + v * s ∈ Ioo (-P.epsilon⁻¹) P.epsilon⁻¹ := by
    rw [hcoord, heq]
    change -R < σ * (-(0.03 : ℝ) * R - s) ∧
      σ * (-(0.03 : ℝ) * R - s) < R
    rcases hσ with rfl | rfl <;> constructor <;>
      nlinarith [hs.1, hs.2, hL.2]
  have hseedCarrier : MapsTo (fun s => P.coordinate_map (q, t₀ + v * s))
      (Icc 0 δ) N.carrier := by
    intro s hs
    change P.coordinate_map (q, t₀ + v * s) ∈ N.carrier
    rw [hcoord]
    apply (hband q (-(0.03 : ℝ) * R - s) ?_).1
    change -(0.08 : ℝ) * R < -(0.03 : ℝ) * R - s ∧
      -(0.03 : ℝ) * R - s < -(0.02 : ℝ) * R
    dsimp only [δ] at hs
    constructor <;> linarith [hs.1, hs.2]
  have hstart := hband q (-(0.03 : ℝ) * R) (by
    change -(0.08 : ℝ) * R < -(0.03 : ℝ) * R ∧
      -(0.03 : ℝ) * R < -(0.02 : ℝ) * R
    constructor <;> linarith)
  have hs₀ : (0.9 : ℝ) * R < s₀ ∧ s₀ < (0.99 : ℝ) * R := hstart.2
  have hdrop :
      (N.coordinate_inverse (P.coordinate_map (q, t₀ + v * δ))).2 < s₀ := by
    have he : t₀ + v * δ = σ * (-(0.07 : ℝ) * R) := by
      dsimp only [t₀, v, δ]
      ring
    rw [he]
    exact horder q
  have hderiv (s : ℝ) (hs : s ∈ Icc 0 L)
      (hcontained : MapsTo (fun r => P.coordinate_map (q, t₀ + v * r))
        (Icc 0 s) N.carrier) :
      (-1.1 : ℝ) ≤ v * deriv (fun t =>
        (N.coordinate_inverse (P.coordinate_map (q, t))).2)
          (t₀ + v * s) ∧
      v * deriv (fun t =>
        (N.coordinate_inverse (P.coordinate_map (q, t))).2)
          (t₀ + v * s) ≤ (-0.9 : ℝ) := by
    apply hprefix N P (hε.trans (min_le_right _ _))
      (heq.trans_le (hε.trans (min_le_right _ _))) q hv hδ hseedCarrier
      hdrop hs.1
      (fun r hr => hdom r ⟨hr.1, hr.2.trans (max_le hδL hs.2)⟩)
      hcontained s
    exact ⟨hs.1, le_rfl⟩
  obtain ⟨hcontained, hheight⟩ := N.axial_segment_contained_of_signed_deriv_bounds_m28
    P q hdom hstart.1
    (rfl : (N.coordinate_inverse (P.coordinate_map (q, t₀))).2 = s₀)
    hderiv
    (by
      apply lt_min <;> change -R < _ <;> linarith [hs₀.1, hL.2])
    (by
      apply max_lt <;> change _ < R <;> linarith [hs₀.2])
  have htarget : t₀ + v * L = (P.coordinate_inverse y).2 := by
    calc
      _ = σ * u := by dsimp only [t₀, v, L]; ring
      _ = _ := by rw [hueq]; rcases hσ with rfl | rfl <;> ring
  have hyEq : P.coordinate_map (q, t₀ + v * L) = y := by
    rw [htarget]
    exact P.coordinate_map_coordinate_inverse hyP
  have hbounds := hheight L ⟨hLpos.le, le_rfl⟩
  rw [hyEq] at hbounds
  refine ⟨hyEq ▸ hcontained ⟨hLpos.le, le_rfl⟩, ?_, ?_⟩
  · have hlower : (0.9 : ℝ) * R - 1.1 * L ≤
        (N.coordinate_inverse y).2 := by
      linarith [hbounds.1, hs₀.1]
    simpa only [R, L] using hlower
  · have hupper : (N.coordinate_inverse y).2 ≤
        (0.99 : ℝ) * R - 0.9 * L := by
      linarith [hbounds.2, hs₀.2]
    simpa only [R, L] using hupper

end PoincareConjecture.EpsilonNeck

namespace PoincareConjecture.M28

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe v

variable {M : Type v} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] in

theorem mem_middle_slab_of_edist_center_le (N : EpsilonNeck g)
    (hε : N.epsilon ≤ 1 / 1000) {x : M}
    (hx : g.edist N.center x ≤
      ENNReal.ofReal ((0.3 : ℝ) * N.scale * N.epsilon⁻¹)) :
    x ∈ N.region (-((0.31 : ℝ) * N.epsilon⁻¹))
      ((0.31 : ℝ) * N.epsilon⁻¹) := by
  by_contra hout
  have hinv : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hlow := N.edist_central_lower_of_not_mem_region
    (mul_pos (by norm_num) hinv)
    (by nlinarith [inv_pos.mpr N.epsilon_pos]) N.center_on_central_sphere hout
  have heps : N.epsilon ≤ (0.001 : ℝ) := by
    norm_num at hε ⊢
    nlinarith [hε]
  have hsq : (0.999 : ℝ) ≤ Real.sqrt (1 - N.epsilon) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [N.epsilon_pos, heps]
  have hcoeff : 0 ≤ (0.31 : ℝ) * N.scale * N.epsilon⁻¹ :=
    mul_nonneg (mul_nonneg (by norm_num) N.scale_pos.le) hinv.le
  have hmul := mul_le_mul_of_nonneg_right hsq hcoeff
  have hlt : ENNReal.ofReal ((0.3 : ℝ) * N.scale * N.epsilon⁻¹) <
      ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon) *
        ((0.31 : ℝ) * N.epsilon⁻¹)) := by
    have hpos : 0 < N.scale * Real.sqrt (1 - N.epsilon) *
        ((0.31 : ℝ) * N.epsilon⁻¹) := by
      have hspos : 0 < Real.sqrt (1 - N.epsilon) :=
        Real.sqrt_pos.2 (by nlinarith [heps])
      exact mul_pos (mul_pos N.scale_pos hspos)
        (mul_pos (by norm_num) hinv)
    apply (ENNReal.ofReal_lt_ofReal_iff hpos).mpr
    have hprod : 0 < N.scale * N.epsilon⁻¹ :=
      mul_pos N.scale_pos hinv
    calc
      (0.3 : ℝ) * N.scale * N.epsilon⁻¹ <
          (0.999 : ℝ) * ((0.31 : ℝ) * N.scale * N.epsilon⁻¹) := by
        nlinarith [hprod]
      _ ≤ Real.sqrt (1 - N.epsilon) *
          ((0.31 : ℝ) * N.scale * N.epsilon⁻¹) := hmul
      _ = N.scale * Real.sqrt (1 - N.epsilon) *
          ((0.31 : ℝ) * N.epsilon⁻¹) := by ring
  exact (not_lt_of_ge (hlow.trans hx)) hlt

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
theorem intrinsicEDist_mono_of_subset {U V : Set M} (hVU : V ⊆ U)
    {p q : M} : intrinsicEDist g U p q ≤ intrinsicEDist g V p q := by
  unfold intrinsicEDist
  apply sInf_le_sInf
  rintro L ⟨γ, hγ, h0, h1, hV, rfl⟩
  exact ⟨γ, hγ, h0, h1, fun x hx => hVU (hV hx), rfl⟩

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
theorem intrinsicEDist_comm_set {U : Set M} {p q : M} :
    intrinsicEDist g U p q = intrinsicEDist g U q p := by
  unfold intrinsicEDist
  have hle : ∀ a b : M,
      sInf {L | ∃ γ : ℝ → M,
        ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc (0 : ℝ) 1) ∧
          γ 0 = a ∧ γ 1 = b ∧ γ '' Icc (0 : ℝ) 1 ⊆ U ∧
            L = g.pathELength γ 0 1} ≤
      sInf {L | ∃ γ : ℝ → M,
        ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc (0 : ℝ) 1) ∧
          γ 0 = b ∧ γ 1 = a ∧ γ '' Icc (0 : ℝ) 1 ⊆ U ∧
            L = g.pathELength γ 0 1} := by
    intro a b
    apply sInf_le_sInf
    rintro L ⟨γ, hγ, h0, h1, hU, rfl⟩
    let rev : ℝ → ℝ := fun t => 1 - t
    have hrev : MapsTo rev (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) := by
      intro t ht
      constructor <;> linarith [ht.1, ht.2]
    have hγrev : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 (γ ∘ rev)
        (Icc (0 : ℝ) 1) := by
      exact hγ.comp ((contMDiff_const.sub contMDiff_id).contMDiffOn) hrev
    have hUrev : (γ ∘ rev) '' Icc (0 : ℝ) 1 ⊆ U := by
      rintro y ⟨t, ht, rfl⟩
      exact hU ⟨rev t, hrev ht, rfl⟩
    have hlen : g.pathELength (γ ∘ rev) 0 1 =
        g.pathELength γ 0 1 := by
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      change Manifold.pathELength (𝓡 3) (γ ∘ rev) 0 1 =
        Manifold.pathELength (𝓡 3) γ 0 1
      simpa only [rev, sub_self, sub_zero] using
        (Manifold.pathELength_comp_of_antitoneOn (I := 𝓡 3) (γ := γ)
          (f := rev) zero_le_one
          (fun _ _ _ _ h => sub_le_sub_left h 1)
          ((differentiable_const (1 : ℝ)).sub differentiable_id).differentiableOn
          (by simpa only [rev, sub_self, sub_zero] using
            hγ.mdifferentiableOn one_ne_zero))
    refine ⟨γ ∘ rev, hγrev, ?_, ?_, hUrev, hlen.symm⟩
    · simpa [rev] using h1
    · simpa [rev] using h0
  exact le_antisymm (hle p q) (hle q p)

theorem anchor_height_lower (N : EpsilonNeck g) (hε : N.epsilon ≤ 1 / 1000)
    (hA : (1000 : ℝ) ≤ N.epsilon⁻¹) {U : Set M}
    (hNU : N.carrier ⊆ U) {z : M} (hz : z ∈ N.carrier)
    (hmin : ENNReal.ofReal ((0.3 : ℝ) * N.scale * N.epsilon⁻¹) ≤
      intrinsicEDist g U N.center z) :
    (0.292 : ℝ) * N.epsilon⁻¹ ≤ |(N.coordinate_inverse z).2| := by
  have hcenter : N.center ∈ N.carrier :=
    N.central_sphere_subset N.center_on_central_sphere
  have hmono := intrinsicEDist_mono_of_subset (g := g) hNU
    (p := N.center) (q := z)
  have hax := N.intrinsicEDist_le_axial_add hcenter hz
  have hcenter0 : (N.coordinate_inverse N.center).2 = 0 :=
    (N.mem_central_sphere_iff_of_mem_carrier hcenter).mp N.center_on_central_sphere
  rw [hcenter0, sub_zero] at hax
  have hbound := hmin.trans (hmono.trans hax)
  have hsqrt : Real.sqrt (1 + N.epsilon) ≤ (1.0005 : ℝ) := by
    have hsqrt0 : 0 ≤ Real.sqrt (1 + N.epsilon) := Real.sqrt_nonneg _
    have hsqrt2 : (Real.sqrt (1 + N.epsilon)) ^ 2 = 1 + N.epsilon := by
      rw [Real.sq_sqrt]
      nlinarith [N.epsilon_pos]
    nlinarith [hsqrt2]
  have hsqrtTwo : Real.sqrt 2 ≤ (1.415 : ℝ) := by
    have hsqrt0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    have hsqrt2 : (Real.sqrt 2) ^ 2 = 2 := by norm_num
    nlinarith [hsqrt2]
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have hreal : (0.3 : ℝ) * N.scale * N.epsilon⁻¹ ≤
      N.scale * Real.sqrt (1 + N.epsilon) *
        (|(N.coordinate_inverse z).2| + Real.sqrt 2 * (Real.pi + 1)) := by
    have hnonneg : 0 ≤ N.scale * Real.sqrt (1 + N.epsilon) *
        (|(N.coordinate_inverse z).2| + Real.sqrt 2 * (Real.pi + 1)) := by
      have hpi0 : 0 ≤ Real.pi := Real.pi_pos.le
      have hsum0 : 0 ≤ |(N.coordinate_inverse z).2| +
          Real.sqrt 2 * (Real.pi + 1) := by
        exact add_nonneg (abs_nonneg _)
          (mul_nonneg (Real.sqrt_nonneg _) (by nlinarith))
      exact mul_nonneg (mul_nonneg N.scale_pos.le (Real.sqrt_nonneg _)) hsum0
    exact (ENNReal.ofReal_le_ofReal_iff hnonneg).mp hbound
  have hscale : 0 < N.scale := N.scale_pos
  have hinv : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hconst : Real.sqrt 2 * (Real.pi + 1) ≤ (7.1 : ℝ) := by
    have hpi0 : 0 ≤ Real.pi := Real.pi_pos.le
    nlinarith [mul_le_mul hsqrtTwo (by nlinarith [hpi])
      (by positivity) (by positivity)]
  have hsum : |(N.coordinate_inverse z).2| +
      Real.sqrt 2 * (Real.pi + 1) ≤ |(N.coordinate_inverse z).2| + 7.1 :=
    by
      linarith [hconst]
  have hfactor : Real.sqrt (1 + N.epsilon) *
      (|(N.coordinate_inverse z).2| + Real.sqrt 2 * (Real.pi + 1)) ≤
      (1.0005 : ℝ) * (|(N.coordinate_inverse z).2| + 7.1) := by
    calc
      _ ≤ (1.0005 : ℝ) *
          (|(N.coordinate_inverse z).2| + Real.sqrt 2 * (Real.pi + 1)) :=
        mul_le_mul_of_nonneg_right hsqrt (by positivity)
      _ ≤ (1.0005 : ℝ) * (|(N.coordinate_inverse z).2| + 7.1) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
  have hupper := mul_le_mul_of_nonneg_left hfactor N.scale_pos.le
  have hcombo : (0.3 : ℝ) * N.scale * N.epsilon⁻¹ ≤
      N.scale * ((1.0005 : ℝ) *
        (|(N.coordinate_inverse z).2| + 7.1)) :=
    hreal.trans (by simpa only [mul_assoc] using hupper)
  nlinarith [mul_le_mul_of_nonneg_left hA N.scale_pos.le]

theorem exists_frontier_high_transition_accuracy :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (1 / 1000 : ℝ) ∧
      ∀ {M : Type v} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}
        (N Q : EpsilonNeck g), N.epsilon = Q.epsilon → N.epsilon ≤ ε₀ →
        ∀ {γ : ℝ → M} {tN tP : ℝ}, tN < tP →
          ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc tN tP) →
          γ tN = N.center → γ tP = Q.center →
          MapsTo γ (Ico tN tP) N.carrier →
          Q.center ∈ frontier N.carrier →
          ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
            ∃ v ∈ Ioo tN tP,
              σ * (N.coordinate_inverse (γ v)).2 =
                (509 : ℝ) * N.epsilon⁻¹ / 512 ∧
              (∀ t ∈ Ioo v tP,
                (509 : ℝ) * N.epsilon⁻¹ / 512 <
                  σ * (N.coordinate_inverse (γ t)).2) ∧
              neckSignedRegion N σ ((127 : ℝ) * N.epsilon⁻¹ / 128)
                  N.epsilon⁻¹ ⊆ Q.carrier := by
  obtain ⟨εF, hFpos, hFsmall, hF⟩ :=
    exists_frontier_neck_sphere_sides_accuracy.{v}
  let ε₀ := min εF (1 / 1000 : ℝ)
  refine ⟨ε₀, lt_min hFpos (by norm_num),
    (min_le_right _ _).trans (by norm_num), ?_⟩
  intro M _ _ _ _ _ _ _ g N Q heq hsmall γ tN tP htp hγ hcN hcQ hγN hfront
  obtain ⟨σ, hσ, v, hv, hvlevel, hafter, _, _, hcap, _⟩ :=
    hF (M := M) (g := g) N.connection N Q heq
      (hsmall.trans (min_le_left _ _)) γ tN tP htp hγ.continuousOn hcN hcQ hγN hfront
  exact ⟨σ, hσ, v, hv, hvlevel, hafter,
    hcap.trans (Q.region_subset_carrier _ _)⟩

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in

theorem intrinsicEDist_triangle_set (U : Set M) {p q r : M} :
    intrinsicEDist g U p r ≤
      intrinsicEDist g U p q + intrinsicEDist g U q r := by
  let d₁ := intrinsicEDist g U p q
  let d₂ := intrinsicEDist g U q r
  by_cases htop : d₁ + d₂ = (⊤ : ℝ≥0∞)
  · simpa only [d₁, d₂, htop] using
      (le_top : intrinsicEDist g U p r ≤ (⊤ : ℝ≥0∞))
  have hfinite : d₁ + d₂ ≠ (⊤ : ℝ≥0∞) := htop
  have h₁finite : d₁ ≠ (⊤ : ℝ≥0∞) :=
    ne_top_of_le_ne_top hfinite le_self_add
  have h₂finite : d₂ ≠ (⊤ : ℝ≥0∞) :=
    ne_top_of_le_ne_top hfinite (by
      exact le_add_left le_rfl)
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  let δ : ℝ≥0∞ := ε / 2
  have hδpos : 0 < δ := by
    dsimp only [δ]
    exact ENNReal.div_pos (ENNReal.coe_pos.mpr hε).ne' (by norm_num)
  obtain ⟨α, hα0, hα1, hα, hαU, hαlen⟩ :=
    exists_intrinsic_competitor g (ENNReal.lt_add_right h₁finite hδpos.ne')
  obtain ⟨β, hβ0, hβ1, hβ, hβU, hβlen⟩ :=
    exists_intrinsic_competitor g (ENNReal.lt_add_right h₂finite hδpos.ne')
  obtain ⟨σ, hσ0, hσ1, hσ, hσU, hσlen⟩ :=
    exists_intrinsic_splice g hα hβ hαU hβU (hα1.trans hβ0.symm)
  have hpath := intrinsicEDist_le_pathELength g zero_le_one hσ hσU
  rw [hσ0, hσ1, hα0, hβ1] at hpath
  calc
    intrinsicEDist g U p r ≤ g.pathELength σ 0 1 := hpath
    _ = g.pathELength α 0 1 + g.pathELength β 0 1 := hσlen
    _ ≤ (d₁ + δ) + (d₂ + δ) := (ENNReal.add_lt_add hαlen hβlen).le
    _ = d₁ + d₂ + ε := by
      dsimp only [δ]
      calc
        (d₁ + ε / 2) + (d₂ + ε / 2) = d₁ + d₂ + (ε / 2 + ε / 2) := by ac_rfl
        _ = d₁ + d₂ + ε := by rw [ENNReal.add_halves]
end PoincareConjecture.M28
