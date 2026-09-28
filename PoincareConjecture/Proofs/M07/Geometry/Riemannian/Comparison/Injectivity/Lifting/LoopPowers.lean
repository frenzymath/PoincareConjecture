import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.Lifting.FiniteFibers
import Mathlib.Data.Fin.Tuple.Basic

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_bounded_loop_powers
    (g : RiemannianMetric n M)
    {f : EuclideanSpace ℝ (Fin n) → M} {R C : ℝ}
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f (Metric.ball 0 R))
    (hbij : ∀ x ∈ Metric.ball 0 R, Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x))
    (hlower : ∀ x ∈ Metric.ball 0 R, ∀ w : EuclideanSpace ℝ (Fin n),
      ‖w‖ / 2 ≤ g.tangentNorm (f x) (mfderiv (𝓡 n) (𝓡 n) f x w))
    {c : ℝ → M} (hc : ∀ t ∈ Icc (0 : ℝ) 1, ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ c t)
    (hC : 0 ≤ C)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) 1, g.tangentNorm (c t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) c t 1) ≤ C)
    (hloop : c 1 = c 0) (hbase : f 0 = c 0)
    (N : ℕ) (hshort : 2 * (N : ℝ) * C < R) :
    ∃ y : Fin (N + 1) → Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R,
      (y 0 : EuclideanSpace ℝ (Fin n)) = 0 ∧
      (∀ i, f (y i) = c 0 ∧ ‖(y i : EuclideanSpace ℝ (Fin n))‖ ≤ 2 * (i : ℝ) * C) ∧
      ∀ i : Fin N, ∃ l : ℝ → Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R,
        ContinuousOn l (Icc 0 1) ∧ l 0 = y i.castSucc ∧ l 1 = y i.succ ∧
        EqOn (fun t => f (l t)) c (Icc 0 1) ∧
        ∀ t ∈ Icc (0 : ℝ) 1,
          ‖(l t : EuclideanSpace ℝ (Fin n)) - y i.castSucc‖ ≤ 2 * C * t := by
  induction N with
  | zero =>
      have hR : 0 < R := by simpa using hshort
      refine ⟨fun _ => ⟨0, by simpa using hR⟩, rfl, ?_, ?_⟩
      · intro i
        have hi : i = 0 := by ext; omega
        subst i
        exact ⟨hbase, by simp⟩
      · exact Fin.elim0
  | succ N ih =>
      have hprev : 2 * (N : ℝ) * C < R := by
        have : (N : ℝ) ≤ (N + 1 : ℕ) := by exact_mod_cast Nat.le_succ N
        nlinarith
      obtain ⟨y, hzero, hy, hsegments⟩ := ih hprev
      have hendshort : ‖(y (Fin.last N) : EuclideanSpace ℝ (Fin n))‖ + 2 * C < R := by
        have h := (hy (Fin.last N)).2
        simp only [Fin.val_last] at h
        push_cast at hshort
        nlinarith
      obtain ⟨l, hl, hlzero, hlproj, hlbound⟩ :=
        exists_bounded_lift_of_lower_differential g hf hbij hlower hc hC hspeed
          (y (Fin.last N)) (hy (Fin.last N)).1 hendshort
      refine ⟨Fin.snoc y (l 1), ?_, ?_, ?_⟩
      · simpa using hzero
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [Fin.snoc_last, Fin.val_last]
          refine ⟨(hlproj (by simp)).trans hloop, ?_⟩
          have h := (hy (Fin.last N)).2
          have hb := hlbound 1 (by simp)
          have ht := norm_add_le
            ((l 1 : EuclideanSpace ℝ (Fin n)) - y (Fin.last N))
            (y (Fin.last N) : EuclideanSpace ℝ (Fin n))
          rw [sub_add_cancel] at ht
          simp only [Fin.val_last, mul_one] at h hb
          push_cast
          nlinarith
        · simpa only [Fin.snoc_castSucc, Fin.val_castSucc] using hy j
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · refine ⟨l, hl, ?_, ?_, hlproj, ?_⟩
          · simpa only [Fin.snoc_castSucc] using hlzero
          · simp
          · simpa only [Fin.snoc_castSucc] using hlbound
        · obtain ⟨k, hk, hkzero, hkone, hkproj, hkbound⟩ := hsegments j
          refine ⟨k, hk, ?_, ?_, hkproj, ?_⟩
          · simpa only [Fin.snoc_castSucc] using hkzero
          · simpa only [← Fin.castSucc_succ, Fin.snoc_castSucc] using hkone
          · simpa only [Fin.snoc_castSucc] using hkbound

theorem exists_bounded_radial_loop_powers
    (g : RiemannianMetric n M)
    {f : EuclideanSpace ℝ (Fin n) → M} {R : ℝ}
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f (Metric.ball 0 R))
    (hbij : ∀ x ∈ Metric.ball 0 R, Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x))
    (hlower : ∀ x ∈ Metric.ball 0 R, ∀ w : EuclideanSpace ℝ (Fin n),
      ‖w‖ / 2 ≤ g.tangentNorm (f x) (mfderiv (𝓡 n) (𝓡 n) f x w))
    (v : EuclideanSpace ℝ (Fin n)) (hreturn : f v = f 0)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (f (t • v))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun u : ℝ => f (u • v)) t 1) ≤ ‖v‖)
    (N : ℕ) (hN : 0 < N) (hshort : 2 * (N : ℝ) * ‖v‖ < R) :
    ∃ y : Fin (N + 1) → Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R,
      (y 0 : EuclideanSpace ℝ (Fin n)) = 0 ∧
      (y ⟨1, by omega⟩ : EuclideanSpace ℝ (Fin n)) = v ∧
      (∀ i, f (y i) = f 0 ∧ ‖(y i : EuclideanSpace ℝ (Fin n))‖ ≤ 2 * (i : ℝ) * ‖v‖) ∧
      ∀ i : Fin N, ∃ l : ℝ → Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R,
        ContinuousOn l (Icc 0 1) ∧ l 0 = y i.castSucc ∧ l 1 = y i.succ ∧
        EqOn (fun t => f (l t)) (fun t : ℝ => f (t • v)) (Icc 0 1) ∧
        ∀ t ∈ Icc (0 : ℝ) 1,
          ‖(l t : EuclideanSpace ℝ (Fin n)) - y i.castSucc‖ ≤ 2 * ‖v‖ * t := by
  have hN' : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hvR : ‖v‖ < R := by nlinarith [norm_nonneg v]
  have htmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : t • v ∈ Metric.ball 0 R := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg v)).trans_lt (by simpa using hvR)
  have hc (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun u : ℝ => f (u • v)) t :=
    (hf.contMDiffAt (Metric.isOpen_ball.mem_nhds (htmem t ht))).comp t
      (contMDiffAt_iff_contDiffAt.mpr (by fun_prop))
  obtain ⟨y, hyzero, hy, hsegments⟩ := exists_bounded_loop_powers g hf hbij hlower hc
    (norm_nonneg v) hspeed (by simpa using hreturn) (by simp) N hshort
  refine ⟨y, hyzero, ?_, ?_, hsegments⟩
  · let i : Fin N := ⟨0, hN⟩
    obtain ⟨l, hl, hlzero, hlone, hlproj, _⟩ := hsegments i
    let B := Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R
    let F := B.domRestrict f
    let k : C(unitInterval, B) :=
      ⟨fun t => l t, hl.comp_continuous continuous_subtype_val (fun t => t.property)⟩
    let r : C(unitInterval, B) :=
      ⟨fun t => ⟨(t : ℝ) • v, htmem t t.property⟩,
        (continuous_subtype_val.smul continuous_const).subtype_mk _⟩
    have hzero : k 0 = r 0 := by
      apply Subtype.ext
      change (l 0 : EuclideanSpace ℝ (Fin n)) = (0 : ℝ) • v
      rw [hlzero, show i.castSucc = 0 from Fin.ext rfl, zero_smul]
      exact hyzero
    have heq := (T2Space.isSeparatedMap F).eq_of_comp_eq
      (isLocalHomeomorph_domRestrict_of_nonsingular Metric.isOpen_ball hf hbij).isLocallyInjective
      k.continuous r.continuous (funext fun t => hlproj t.property) 0 hzero
    have hend := congrArg Subtype.val (congrFun heq 1)
    change (l 1 : EuclideanSpace ℝ (Fin n)) = (1 : ℝ) • v at hend
    rw [hlone, one_smul] at hend
    exact hend
  · simpa only [zero_smul] using hy

end PoincareConjecture
