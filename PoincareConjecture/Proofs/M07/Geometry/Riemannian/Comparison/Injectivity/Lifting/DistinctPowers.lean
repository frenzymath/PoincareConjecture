import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.Lifting.DeckOrbit

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem injective_loop_powers_of_no_deck_period
    {f : EuclideanSpace ℝ (Fin n) → M} {R a : ℝ}
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f (Metric.ball 0 R))
    (hbij : ∀ x ∈ Metric.ball 0 R, Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x))
    {v : EuclideanSpace ℝ (Fin n)} {N : ℕ} (hN : 0 < N)
    (hmargin : ‖v‖ + 4 * (N : ℝ) * ‖v‖ < R)
    (ha : 0 < a) (hiter : ‖v‖ + 2 * ((2 : ℝ) ^ N * (a + ‖v‖)) < R)
    {d : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hd : ContDiffOn ℝ ∞ d {x | ‖v‖ + 2 * ‖x‖ < R})
    (hdmem : MapsTo d {x | ‖v‖ + 2 * ‖x‖ < R} (Metric.ball 0 R))
    (hdproj : EqOn (f ∘ d) f {x | ‖v‖ + 2 * ‖x‖ < R}) (hdzero : d 0 = v)
    (hdbound : ∀ x ∈ {x | ‖v‖ + 2 * ‖x‖ < R}, ‖d x - v‖ ≤ 2 * ‖x‖)
    (hnoperiod : ∀ m : ℕ, 0 < m → m ≤ N → ¬EqOn (d^[m]) id (Metric.ball 0 a))
    (y : Fin (N + 1) → Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)
    (hyzero : (y 0 : EuclideanSpace ℝ (Fin n)) = 0)
    (hyone : (y ⟨1, by omega⟩ : EuclideanSpace ℝ (Fin n)) = v)
    (hybound : ∀ i, ‖(y i : EuclideanSpace ℝ (Fin n))‖ ≤ 2 * (i : ℝ) * ‖v‖)
    (hsegments : ∀ i : Fin N, ∃ l : ℝ → Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R,
      ContinuousOn l (Icc 0 1) ∧ l 0 = y i.castSucc ∧ l 1 = y i.succ ∧
      EqOn (fun t => f (l t)) (fun t : ℝ => f (t • v)) (Icc 0 1) ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        ‖(l t : EuclideanSpace ℝ (Fin n)) - y i.castSucc‖ ≤ 2 * ‖v‖ * t) :
    Injective (fun i => (y i : EuclideanSpace ℝ (Fin n))) := by
  have hstep := deck_motion_maps_loop_powers hf hbij hN hmargin hd.continuousOn
    hdmem hdproj hdzero y hyzero hyone hybound hsegments
  have hiterates := loop_powers_eq_iterate d
    (fun i => (y i : EuclideanSpace ℝ (Fin n))) hyzero hstep
  have hcollision (i j : Fin (N + 1)) (hij : i < j) (heq : y i = y j) : False := by
    have hsegments' : ∀ i : Fin N, ∃ l : ℝ → Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R,
        ContinuousOn l (Icc 0 1) ∧ l 0 = y i.castSucc ∧ l 1 = y i.succ ∧
        EqOn (fun t => f (l t)) (fun t : ℝ => f (t • v)) (Icc 0 1) := by
      intro i
      obtain ⟨l, hl, hzero, hone, hproj, _⟩ := hsegments i
      exact ⟨l, hl, hzero, hone, hproj⟩
    obtain ⟨k, hkpos, hkzero⟩ :=
      loop_power_collision_produces_return hf hbij y hsegments' i j hij heq
    have hkN : k.val ≤ N := by omega
    have hreturn : d^[k.val] 0 = 0 := by rw [hiterates k, hkzero, hyzero]
    exact hnoperiod k hkpos hkN
      (deck_motion_iterate_eqOn_id_of_return hf hbij hd hdproj hdbound N ha hiter k hkN hreturn)
  intro i j heq
  rcases lt_trichotomy i j with hij | hij | hij
  · exact (hcollision i j hij (Subtype.ext heq)).elim
  · exact hij
  · exact (hcollision j i hij (Subtype.ext heq.symm)).elim

def loopOrbitRadius (s : ℝ) (N : ℕ) : ℝ := s / (16 * (2 : ℝ) ^ N)

def loopPowerThreshold (s : ℝ) (N : ℕ) : ℝ :=
  s / (1024 * ((N : ℝ) + 1) ^ 4 * (4 : ℝ) ^ N)

theorem loopOrbitRadius_pos {s : ℝ} (hs : 0 < s) (N : ℕ) :
    0 < loopOrbitRadius s N := by
  unfold loopOrbitRadius
  positivity

theorem loopPowerThreshold_pos {s : ℝ} (hs : 0 < s) (N : ℕ) :
    0 < loopPowerThreshold s N := by
  unfold loopPowerThreshold
  positivity

theorem loopPowerThreshold_margins {s ell : ℝ} (hs : 0 < s) (hell : 0 ≤ ell)
    (N : ℕ) (hshort : ell ≤ loopPowerThreshold s N) :
    ell + 4 * (N : ℝ) * ell < s ∧
    ell + 2 * ((2 : ℝ) ^ N * (loopOrbitRadius s N + ell)) < s := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hbase : (1 : ℝ) ≤ N + 1 := by linarith
  have hp4 : ((N : ℝ) + 1) ≤ ((N : ℝ) + 1) ^ 4 := by
    nlinarith [sq_nonneg (N : ℝ), sq_nonneg ((N : ℝ) ^ 2)]
  have hp4one : (1 : ℝ) ≤ ((N : ℝ) + 1) ^ 4 := hbase.trans hp4
  have htwo : (1 : ℝ) ≤ (2 : ℝ) ^ N := one_le_pow₀ (by norm_num)
  have hfour : (2 : ℝ) ^ N ≤ (4 : ℝ) ^ N := by gcongr; norm_num
  have hfourone : (1 : ℝ) ≤ (4 : ℝ) ^ N := htwo.trans hfour
  have hden : 0 < 1024 * ((N : ℝ) + 1) ^ 4 * (4 : ℝ) ^ N := by positivity
  have hcap : ell * (1024 * ((N : ℝ) + 1) ^ 4 * (4 : ℝ) ^ N) ≤ s :=
    (le_div_iff₀ hden).mp hshort
  have hcoefftwo : 1024 * (2 : ℝ) ^ N ≤
      1024 * ((N : ℝ) + 1) ^ 4 * (4 : ℝ) ^ N := by
    calc
      _ ≤ 1024 * (4 : ℝ) ^ N := by gcongr
      _ ≤ _ := by nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) N]
  have hcoeffN : 1024 * (N : ℝ) ≤
      1024 * ((N : ℝ) + 1) ^ 4 * (4 : ℝ) ^ N := by
    calc
      _ ≤ 1024 * ((N : ℝ) + 1) ^ 4 := by nlinarith
      _ ≤ _ := by nlinarith [pow_nonneg (show (0 : ℝ) ≤ N + 1 by positivity) 4]
  have htwoell : 1024 * (2 : ℝ) ^ N * ell ≤ s := by
    nlinarith [mul_le_mul_of_nonneg_right hcoefftwo hell]
  have hNell : 1024 * (N : ℝ) * ell ≤ s := by
    nlinarith [mul_le_mul_of_nonneg_right hcoeffN hell]
  have hellcap : 1024 * ell ≤ s := by nlinarith [mul_le_mul_of_nonneg_right htwo hell]
  have haradius : (2 : ℝ) ^ N * loopOrbitRadius s N = s / 16 := by
    unfold loopOrbitRadius
    field_simp
  constructor
  · nlinarith
  · rw [mul_add, haradius]
    nlinarith

end PoincareConjecture
