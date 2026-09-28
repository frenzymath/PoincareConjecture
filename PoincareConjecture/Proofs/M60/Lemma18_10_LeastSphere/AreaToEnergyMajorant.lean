import PoincareConjecture.Proofs.M60.Mathlib.UniformizationBundleForms
import Mathlib.Geometry.Manifold.PartitionOfUnity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Set Filter
open scoped Manifold ContDiff Topology

universe u

noncomputable section

namespace PoincareConjecture

local notation "E" => LoopPlane
local notation "T" => TangentSpace (𝓡 2) (M := UnitTwoSphere)
local notation "V" => (fun p : UnitTwoSphere => T p →L[ℝ] T p →L[ℝ] ℝ)

local instance majorantTangentNormedAddCommGroup (p : UnitTwoSphere) :
    NormedAddCommGroup (T p) :=
  inferInstanceAs (NormedAddCommGroup E)

local instance majorantTangentNormedSpace (p : UnitTwoSphere) : NormedSpace ℝ (T p) :=
  inferInstanceAs (NormedSpace ℝ E)

local instance majorantCotangentContinuousAdd :
    ∀ p : UnitTwoSphere, ContinuousAdd (T p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (E →L[ℝ] ℝ))

local instance majorantFormAddCommGroup : ∀ p : UnitTwoSphere, AddCommGroup (V p) :=
  fun _ => inferInstanceAs (AddCommGroup (E →L[ℝ] E →L[ℝ] ℝ))

local instance majorantFormModule : ∀ p : UnitTwoSphere, Module ℝ (V p) :=
  fun _ => inferInstanceAs (Module ℝ (E →L[ℝ] E →L[ℝ] ℝ))

private theorem convex_symmetric_form_interval (L H : E →L[ℝ] E →L[ℝ] ℝ) :
    Convex ℝ {B : E →L[ℝ] E →L[ℝ] ℝ | (∀ v w, B v w = B w v) ∧
      ∀ v, v ≠ 0 → L v v < B v v ∧ B v v < H v v} := by
  intro B hB C hC a b ha hb hab
  refine ⟨?_, ?_⟩
  · intro v w
    simp only [add_apply, smul_apply, smul_eq_mul, hB.1 v w, hC.1 v w]
  · intro v hv
    have hBv := hB.2 v hv
    have hCv := hC.2 v hv
    simp only [add_apply, smul_apply, smul_eq_mul]
    by_cases haz : a = 0
    · have hb1 : b = 1 := by linarith
      simpa only [haz, hb1, zero_mul, one_mul, zero_add] using hCv
    · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
      have hlow := add_lt_add_of_lt_of_le
        (mul_lt_mul_of_pos_left hBv.1 hap) (mul_le_mul_of_nonneg_left hCv.1.le hb)
      have hupp := add_lt_add_of_lt_of_le
        (mul_lt_mul_of_pos_left hBv.2 hap) (mul_le_mul_of_nonneg_left hCv.2.le hb)
      rw [← add_mul, hab, one_mul] at hlow hupp
      exact ⟨hlow, hupp⟩

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option maxHeartbeats 800000 in

theorem m60Sphere_exists_smooth_metric_majorant (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f)
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ q : RiemannianMetric 2 UnitTwoSphere,
      ∀ (p : UnitTwoSphere) (v : T p),
        M60.metricPullbackForm (n := 2) g f p v v +
          delta * m60RoundSphereMetric.inner p v v ≤ q.inner p v v ∧
        q.inner p v v ≤ M60.metricPullbackForm (n := 2) g f p v v +
          2 * delta * m60RoundSphereMetric.inner p v v := by
  let A := M60.metricPullbackForm (n := 2) g f
  let R := m60RoundSphereMetric.inner
  let L : (p : UnitTwoSphere) → V p := fun p => A p + delta • R p
  let H : (p : UnitTwoSphere) → V p := fun p => A p + (2 * delta) • R p
  let t : (p : UnitTwoSphere) → Set (V p) := fun p =>
    {B | (∀ v w, B v w = B w v) ∧ ∀ v, v ≠ 0 → L p v v < B v v ∧ B v v < H p v v}
  have hA (p : UnitTwoSphere) :
      ContMDiffAt (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 0
        (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (A x)) p :=
    M60.spherePullbackForm_contMDiffAt_zero g (hf p)
  have hR (p : UnitTwoSphere) :
      ContMDiffAt (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 0
        (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (R x)) p :=
    (m60RoundSphereMetric.contMDiff p).of_le (by simp)
  have hloc (p : UnitTwoSphere) : ∃ U ∈ 𝓝 p, ∃ s : (x : UnitTwoSphere) → V x,
      ContMDiffOn (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (s x)) U ∧
      ∀ x ∈ U, s x ∈ t x := by
    let B := A p + ((3 / 2 : ℝ) * delta) • R p
    have hB : ∀ v w, B v w = B w v := by
      intro v w
      change g.inner (f p) (mfderiv (𝓡 2) (𝓡 n) f p v) (mfderiv (𝓡 2) (𝓡 n) f p w) +
        _ * m60RoundSphereMetric.inner p v w = _
      rw [g.symm, m60RoundSphereMetric.symm]
      rfl
    obtain ⟨U, hU, s, hs, hsp, hsym⟩ := M60.exists_local_smooth_symmetric_sphere_form p B hB
    have hs₀ := ((hs p (mem_of_mem_nhds hU)).contMDiffAt hU).of_le (show 0 ≤ ∞ by simp)
    have hlow : ∀ᶠ x in 𝓝 p, ∀ v : T x, v ≠ 0 → 0 < (s x - L x) v v := by
      apply M60.eventually_positive_sphere_form (fun x => s x - L x)
        (hs₀.sub_section ((hA p).add_section ((hR p).const_smul_section))).continuousAt
      intro v hv
      rw [hsp]
      change 0 < A p v v + ((3 / 2 : ℝ) * delta) * R p v v -
        (A p v v + delta * R p v v)
      have hr : 0 < R p v v := m60RoundSphereMetric.pos p v hv
      nlinarith [mul_pos hdelta hr]
    have hupp : ∀ᶠ x in 𝓝 p, ∀ v : T x, v ≠ 0 → 0 < (H x - s x) v v := by
      apply M60.eventually_positive_sphere_form (fun x => H x - s x)
        (((hA p).add_section ((hR p).const_smul_section)).sub_section hs₀).continuousAt
      intro v hv
      rw [hsp]
      change 0 < (A p v v + (2 * delta) * R p v v) -
        (A p v v + ((3 / 2 : ℝ) * delta) * R p v v)
      have hr : 0 < R p v v := m60RoundSphereMetric.pos p v hv
      nlinarith [mul_pos hdelta hr]
    refine ⟨U ∩ {x | (∀ v : T x, v ≠ 0 → 0 < (s x - L x) v v) ∧
      ∀ v : T x, v ≠ 0 → 0 < (H x - s x) v v},
      inter_mem hU (hlow.and hupp), s, hs.mono inter_subset_left, ?_⟩
    intro x hx
    refine ⟨hsym x hx.1, ?_⟩
    intro v hv
    have hlo := hx.2.1 v hv
    have hhi := hx.2.2 v hv
    change 0 < s x v v - L x v v at hlo
    change 0 < H x v v - s x v v at hhi
    exact ⟨sub_pos.mp hlo, sub_pos.mp hhi⟩
  obtain ⟨s, hs⟩ := exists_contMDiffSection_forall_mem_convex_of_local (𝓡 2) V t
    (fun p => convex_symmetric_form_interval (L p) (H p)) hloc
  have hnonneg (p : UnitTwoSphere) (v : T p) : 0 ≤ A p v v := by
    change 0 ≤ g.inner (f p) (mfderiv (𝓡 2) (𝓡 n) f p v) (mfderiv (𝓡 2) (𝓡 n) f p v)
    by_cases hv : mfderiv (𝓡 2) (𝓡 n) f p v = 0
    · simp [hv]
    · exact (g.pos _ _ hv).le
  have hbounds (p : UnitTwoSphere) (v : T p) : L p v v ≤ s p v v ∧ s p v v ≤ H p v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact ⟨((hs p).2 v hv).1.le, ((hs p).2 v hv).2.le⟩
  let q : RiemannianMetric 2 UnitTwoSphere := {
    inner := s
    symm := fun p => (hs p).1
    pos := fun p v hv => by
      have h := (hbounds p v).1
      change A p v v + delta * R p v v ≤ s p v v at h
      exact lt_of_lt_of_le
        (add_pos_of_nonneg_of_pos (hnonneg p v)
          (mul_pos hdelta (m60RoundSphereMetric.pos p v hv))) h
    isVonNBounded := fun p => by
      let D : T p →L[ℝ] T p := (Real.sqrt delta)⁻¹ • ContinuousLinearMap.id ℝ (T p)
      refine ((m60RoundSphereMetric.isVonNBounded p).image D).subset ?_
      intro v hv
      refine ⟨Real.sqrt delta • v, ?_, ?_⟩
      · change R p (Real.sqrt delta • v) (Real.sqrt delta • v) < 1
        simp only [map_smul, smul_apply, smul_eq_mul]
        rw [← mul_assoc, Real.mul_self_sqrt hdelta.le]
        have h := (hbounds p v).1
        change A p v v + delta * R p v v ≤ s p v v at h
        change s p v v < 1 at hv
        linarith [hnonneg p v]
      · change (Real.sqrt delta)⁻¹ • (Real.sqrt delta • v) = v
        rw [smul_smul, inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr hdelta), one_smul]
    contMDiff := s.contMDiff }
  exact ⟨q, hbounds⟩

end PoincareConjecture

end
