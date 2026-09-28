import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.Lifting.LoopPowers
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.Lifting.SmoothDeck

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem eqOn_deck_motion_comp_lift
    {f : EuclideanSpace ℝ (Fin n) → M} {R : ℝ}
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f (Metric.ball 0 R))
    (hbij : ∀ x ∈ Metric.ball 0 R, Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x))
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {d : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hd : ContinuousOn d U) (hdmem : MapsTo d U (Metric.ball 0 R))
    (hdproj : EqOn (f ∘ d) f U)
    {l k : ℝ → Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R}
    (hl : ContinuousOn l (Icc (0 : ℝ) 1)) (hk : ContinuousOn k (Icc (0 : ℝ) 1))
    (hlmem : ∀ t ∈ Icc (0 : ℝ) 1, (l t : EuclideanSpace ℝ (Fin n)) ∈ U)
    (hproj : EqOn (fun t => f (l t)) (fun t => f (k t)) (Icc (0 : ℝ) 1))
    (hzero : d (l 0) = k 0) :
    EqOn (fun t => d (l t)) (fun t => (k t : EuclideanSpace ℝ (Fin n))) (Icc (0 : ℝ) 1) := by
  let B := Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R
  let F := B.domRestrict f
  let a : C(unitInterval, B) :=
    ⟨fun t => ⟨d (l t), hdmem (hlmem t t.property)⟩,
      (hd.comp_continuous
        (continuous_subtype_val.comp (hl.comp_continuous continuous_subtype_val
          (fun t => t.property))) (fun t => hlmem t t.property)).subtype_mk _⟩
  let b : C(unitInterval, B) :=
    ⟨fun t => k t, hk.comp_continuous continuous_subtype_val (fun t => t.property)⟩
  have heq := (T2Space.isSeparatedMap F).eq_of_comp_eq
    (isLocalHomeomorph_domRestrict_of_nonsingular Metric.isOpen_ball hf hbij).isLocallyInjective
    a.continuous b.continuous (funext fun t =>
      (hdproj (hlmem t t.property)).trans (hproj t.property)) 0 (Subtype.ext hzero)
  intro t ht
  exact congrArg Subtype.val (congrFun heq ⟨t, ht⟩)

theorem deck_motion_maps_loop_powers
    {f : EuclideanSpace ℝ (Fin n) → M} {R : ℝ}
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f (Metric.ball 0 R))
    (hbij : ∀ x ∈ Metric.ball 0 R, Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x))
    {v : EuclideanSpace ℝ (Fin n)} {N : ℕ} (hN : 0 < N)
    (hmargin : ‖v‖ + 4 * (N : ℝ) * ‖v‖ < R)
    {d : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hd : ContinuousOn d {x | ‖v‖ + 2 * ‖x‖ < R})
    (hdmem : MapsTo d {x | ‖v‖ + 2 * ‖x‖ < R} (Metric.ball 0 R))
    (hdproj : EqOn (f ∘ d) f {x | ‖v‖ + 2 * ‖x‖ < R}) (hdzero : d 0 = v)
    (y : Fin (N + 1) → Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)
    (hyzero : (y 0 : EuclideanSpace ℝ (Fin n)) = 0)
    (hyone : (y ⟨1, by omega⟩ : EuclideanSpace ℝ (Fin n)) = v)
    (hybound : ∀ i, ‖(y i : EuclideanSpace ℝ (Fin n))‖ ≤ 2 * (i : ℝ) * ‖v‖)
    (hsegments : ∀ i : Fin N, ∃ l : ℝ → Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R,
      ContinuousOn l (Icc 0 1) ∧ l 0 = y i.castSucc ∧ l 1 = y i.succ ∧
      EqOn (fun t => f (l t)) (fun t : ℝ => f (t • v)) (Icc 0 1) ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        ‖(l t : EuclideanSpace ℝ (Fin n)) - y i.castSucc‖ ≤ 2 * ‖v‖ * t) :
    ∀ i : Fin N, d (y i.castSucc) = y i.succ := by
  have hstep (j : ℕ) (hj : j < N) :
      d (y ⟨j, by omega⟩) = y ⟨j + 1, by omega⟩ := by
    induction j with
    | zero => simpa only [Fin.mk_zero, hyzero, hdzero] using hyone.symm
    | succ j ih =>
      let i : Fin N := ⟨j, by omega⟩
      let i' : Fin N := ⟨j + 1, hj⟩
      obtain ⟨l, hl, hlzero, hlone, hlproj, hlbound⟩ := hsegments i
      obtain ⟨k, hk, hkzero, hkone, hkproj, _⟩ := hsegments i'
      have hlmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
          (l t : EuclideanSpace ℝ (Fin n)) ∈ {x | ‖v‖ + 2 * ‖x‖ < R} := by
        have hb := hlbound t ht
        have hyb := hybound i.castSucc
        have htri := norm_add_le
          ((l t : EuclideanSpace ℝ (Fin n)) - y i.castSucc)
          (y i.castSucc : EuclideanSpace ℝ (Fin n))
        rw [sub_add_cancel] at htri
        have hij : (j : ℝ) + 1 ≤ N := by exact_mod_cast Nat.succ_le_of_lt i.is_lt
        have hmul := mul_le_mul_of_nonneg_left ht.2 (show 0 ≤ 2 * ‖v‖ by positivity)
        have hmul' := mul_le_mul_of_nonneg_right hij (norm_nonneg v)
        simp only [i, Fin.val_castSucc] at hyb
        change ‖v‖ + 2 * ‖(l t : EuclideanSpace ℝ (Fin n))‖ < R
        nlinarith
      have hzero : d (l 0) = k 0 := by
        rw [hlzero, hkzero]
        exact ih (by omega)
      have heq := eqOn_deck_motion_comp_lift hf hbij hd hdmem hdproj hl hk hlmem
        (hlproj.trans hkproj.symm) hzero
      have hend := heq (by simp : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
      change d (l 1) = (k 1 : EuclideanSpace ℝ (Fin n)) at hend
      rw [hlone, hkone] at hend
      exact hend
  intro i
  exact hstep i i.is_lt

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] in

theorem deck_motion_iterates_controlled
    {f : EuclideanSpace ℝ (Fin n) → M} {R a : ℝ}
    {v : EuclideanSpace ℝ (Fin n)}
    {d : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hd : ContDiffOn ℝ ∞ d {x | ‖v‖ + 2 * ‖x‖ < R})
    (hdproj : EqOn (f ∘ d) f {x | ‖v‖ + 2 * ‖x‖ < R})
    (hdbound : ∀ x ∈ {x | ‖v‖ + 2 * ‖x‖ < R}, ‖d x - v‖ ≤ 2 * ‖x‖)
    (N : ℕ) (hmargin : ‖v‖ + 2 * ((2 : ℝ) ^ N * (a + ‖v‖)) < R) :
    ∀ i ≤ N,
      ContDiffOn ℝ ∞ (d^[i]) (Metric.ball 0 a) ∧
      MapsTo (d^[i]) (Metric.ball 0 a) {x | ‖v‖ + 2 * ‖x‖ < R} ∧
      EqOn (f ∘ d^[i]) f (Metric.ball 0 a) ∧
      ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) a,
        ‖d^[i] x‖ + ‖v‖ ≤ (2 : ℝ) ^ i * (‖x‖ + ‖v‖) := by
  have hmem (i : ℕ) (hi : i ≤ N) (x : EuclideanSpace ℝ (Fin n))
      (hx : x ∈ Metric.ball 0 a)
      (hb : ‖d^[i] x‖ + ‖v‖ ≤ (2 : ℝ) ^ i * (‖x‖ + ‖v‖)) :
      d^[i] x ∈ {x | ‖v‖ + 2 * ‖x‖ < R} := by
    have hx' : ‖x‖ < a := by simpa using hx
    have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hi
    have hmul := mul_le_mul_of_nonneg_right hpow (add_nonneg (norm_nonneg x) (norm_nonneg v))
    have hmul' := mul_le_mul_of_nonneg_left (le_of_lt hx') (by positivity : 0 ≤ (2 : ℝ) ^ N)
    change ‖v‖ + 2 * ‖d^[i] x‖ < R
    nlinarith [norm_nonneg v]
  intro i hi
  induction i with
  | zero =>
      refine ⟨contDiffOn_id, ?_, ?_, ?_⟩
      · intro x hx
        exact hmem 0 hi x hx (by simp)
      · intro x hx
        rfl
      · intro x hx
        simp
  | succ i ih =>
      obtain ⟨his, himem, hiproj, hibound⟩ := ih (by omega)
      have hb (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.ball 0 a) :
          ‖d^[i + 1] x‖ + ‖v‖ ≤ (2 : ℝ) ^ (i + 1) * (‖x‖ + ‖v‖) := by
        have h := hdbound (d^[i] x) (himem hx)
        have htri := norm_add_le (d (d^[i] x) - v) v
        rw [sub_add_cancel] at htri
        rw [Function.iterate_succ_apply', pow_succ]
        nlinarith [hibound x hx]
      refine ⟨?_, fun x hx => hmem (i + 1) hi x hx (hb x hx), ?_, hb⟩
      · simpa only [Function.iterate_succ'] using hd.comp his himem
      · intro x hx
        change f (d^[i + 1] x) = f x
        rw [Function.iterate_succ_apply']
        exact (hdproj (himem hx)).trans (hiproj hx)

theorem deck_motion_iterate_eqOn_id_of_return
    {f : EuclideanSpace ℝ (Fin n) → M} {R a : ℝ}
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f (Metric.ball 0 R))
    (hbij : ∀ x ∈ Metric.ball 0 R, Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x))
    {v : EuclideanSpace ℝ (Fin n)}
    {d : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hd : ContDiffOn ℝ ∞ d {x | ‖v‖ + 2 * ‖x‖ < R})
    (hdproj : EqOn (f ∘ d) f {x | ‖v‖ + 2 * ‖x‖ < R})
    (hdbound : ∀ x ∈ {x | ‖v‖ + 2 * ‖x‖ < R}, ‖d x - v‖ ≤ 2 * ‖x‖)
    (N : ℕ) (ha : 0 < a) (hmargin : ‖v‖ + 2 * ((2 : ℝ) ^ N * (a + ‖v‖)) < R)
    (i : ℕ) (hi : i ≤ N) (hreturn : d^[i] 0 = 0) :
    EqOn (d^[i]) id (Metric.ball 0 a) := by
  obtain ⟨his, himem, hiproj, _⟩ :=
    deck_motion_iterates_controlled hd hdproj hdbound N hmargin i hi
  have hUsub : {x : EuclideanSpace ℝ (Fin n) | ‖v‖ + 2 * ‖x‖ < R} ⊆
      Metric.ball 0 R := by
    intro x hx
    rw [Metric.mem_ball, dist_zero_right]
    change ‖v‖ + 2 * ‖x‖ < R at hx
    linarith [norm_nonneg v, norm_nonneg x]
  have hsmall : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) a ⊆ Metric.ball 0 R := by
    intro x hx
    exact hUsub ((deck_motion_iterates_controlled hd hdproj hdbound N hmargin 0
      (Nat.zero_le N)).2.1 hx)
  let A := Metric.ball (0 : EuclideanSpace ℝ (Fin n)) a
  let B := Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R
  let F := B.domRestrict f
  let s : C(A, B) := ⟨fun x => ⟨d^[i] x, hUsub (himem x.property)⟩,
    (his.continuousOn.comp_continuous continuous_subtype_val
      (fun x => x.property)).subtype_mk _⟩
  let t : C(A, B) := ⟨fun x => ⟨x, hsmall x.property⟩,
    continuous_subtype_val.subtype_mk _⟩
  have : PreconnectedSpace A := isPreconnected_iff_preconnectedSpace.mp
    (convex_ball (0 : EuclideanSpace ℝ (Fin n)) a).isPreconnected
  have heq := (T2Space.isSeparatedMap F).eq_of_comp_eq
    (isLocalHomeomorph_domRestrict_of_nonsingular Metric.isOpen_ball hf hbij).isLocallyInjective
    s.continuous t.continuous (funext fun x => hiproj x.property)
    ⟨0, by simpa [A] using ha⟩ (Subtype.ext hreturn)
  intro x hx
  exact congrArg Subtype.val (congrFun heq ⟨x, hx⟩)

theorem loop_powers_eq_iterate
    {E : Type*} [Zero E] {N : ℕ} (d : E → E) (y : Fin (N + 1) → E)
    (hzero : y 0 = 0) (hstep : ∀ i : Fin N, d (y i.castSucc) = y i.succ) :
    ∀ i : Fin (N + 1), d^[i.val] 0 = y i := by
  have h (i : ℕ) (hi : i ≤ N) : d^[i] 0 = y ⟨i, by omega⟩ := by
    induction i with
    | zero => simpa using hzero.symm
    | succ i ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      exact hstep ⟨i, by omega⟩
  intro i
  exact h i (by omega)

theorem loop_power_collision_produces_return
    {f : EuclideanSpace ℝ (Fin n) → M} {R : ℝ}
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f (Metric.ball 0 R))
    (hbij : ∀ x ∈ Metric.ball 0 R, Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x))
    {N : ℕ} {c : ℝ → M}
    (y : Fin (N + 1) → Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)
    (hsegments : ∀ i : Fin N, ∃ l : ℝ → Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R,
      ContinuousOn l (Icc 0 1) ∧ l 0 = y i.castSucc ∧ l 1 = y i.succ ∧
      EqOn (fun t => f (l t)) c (Icc 0 1))
    (i j : Fin (N + 1)) (hij : i < j) (heq : y i = y j) :
    ∃ k : Fin (N + 1), 0 < k.val ∧ y k = y 0 := by
  have hpred (p q : Fin N) (hpq : y p.succ = y q.succ) :
      y p.castSucc = y q.castSucc := by
    obtain ⟨l, hl, hlzero, hlone, hlproj⟩ := hsegments p
    obtain ⟨k, hk, hkzero, hkone, hkproj⟩ := hsegments q
    have heq := (T2Space.isSeparatedMap
      ((Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R).domRestrict f)).eqOn_of_comp_eqOn
      (isLocalHomeomorph_domRestrict_of_nonsingular Metric.isOpen_ball hf hbij).isLocallyInjective
      isPreconnected_Icc hl hk (hlproj.trans hkproj.symm)
      (by simp : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
      (by simpa only [hlone, hkone] using hpq)
    simpa only [hlzero, hkzero] using heq (by simp : (0 : ℝ) ∈ Icc (0 : ℝ) 1)
  have hcancel (p q : ℕ) (hp : p ≤ N) (hq : q ≤ N) (hpq : p < q)
      (heq : y ⟨p, by omega⟩ = y ⟨q, by omega⟩) :
      y ⟨q - p, by omega⟩ = y 0 := by
    induction p generalizing q with
    | zero => simpa using heq.symm
    | succ p ih =>
      have hqpos : 0 < q := by omega
      obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
      have h := hpred ⟨p, by omega⟩ ⟨q, by omega⟩ heq
      simpa using ih q (by omega) (by omega) (by omega) h
  exact ⟨⟨j.val - i.val, by omega⟩, Nat.sub_pos_of_lt hij,
    hcancel i j (by omega) (by omega) hij heq⟩

end PoincareConjecture
