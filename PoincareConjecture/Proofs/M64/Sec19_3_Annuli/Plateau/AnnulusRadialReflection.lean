import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialFixedTrace
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.PlaneReflection
import PoincareConjecture.Proofs.M60.Mathlib.LipschitzGluing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace PoincareConjecture

def m64RadialLowerFold (p : LoopPlane) : LoopPlane :=
  if p 1 ≤ 0 then p else m60PlaneReflection p

theorem m64RadialLowerFold_lipschitz : LipschitzWith 1 m64RadialLowerFold := by
  have h := M60.lipschitzOnWith_piecewise_of_convex (convex_univ : Convex ℝ (univ : Set LoopPlane))
    (fun p => p 1) (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous.continuousOn 0
    (LipschitzWith.id.lipschitzOnWith.mono inter_subset_left)
    (m60PlaneReflection.lipschitz.lipschitzOnWith.mono inter_subset_left) (by
      intro p _ hp
      ext i
      fin_cases i <;> simp [m60PlaneReflection_apply, hp])
  simpa +instances only [max_self, lipschitzOnWith_univ, piecewise, mem_ofPred_eq,
    m64RadialLowerFold, id_eq] using! h

theorem m64RadialLowerFold_eq_self {p : LoopPlane} (hp : p 1 ≤ 0) :
    m64RadialLowerFold p = p := if_pos hp

theorem m64RadialLowerFold_eq_reflection {p : LoopPlane} (hp : 0 ≤ p 1) :
    m64RadialLowerFold p = m60PlaneReflection p := by
  by_cases h : p 1 ≤ 0
  · rw [m64RadialLowerFold_eq_self h]
    ext i
    fin_cases i <;> simp [m60PlaneReflection_apply, le_antisymm h hp]
  · exact if_neg h

theorem m64PlaneReflection_fixed {a : LoopPlane} (ha : a 1 = 0) :
    m60PlaneReflection a = a := by
  ext i
  fin_cases i <;> simp [m60PlaneReflection_apply, ha]

theorem m64RadialLowerFold_mem_closedBall {a p : LoopPlane} (ha : a 1 = 0)
    {r : ℝ} (hp : p ∈ closedBall a r) : m64RadialLowerFold p ∈ closedBall a r := by
  by_cases hy : p 1 ≤ 0
  · rwa [m64RadialLowerFold_eq_self hy]
  · rw [m64RadialLowerFold_eq_reflection (le_of_not_ge hy), mem_closedBall,
      ← m64PlaneReflection_fixed ha, m60PlaneReflection.dist_map]
    exact hp

def m64RadialCorrect {E : Type*} [AddCommGroup E]
    (f h : LoopPlane → E) (p : LoopPlane) : E :=
  f p - f (m64RadialLowerFold p) + h p

theorem m64RadialCorrect_lower {E : Type*} [AddCommGroup E]
    (f h : LoopPlane → E) {p : LoopPlane} (hp : p 1 ≤ 0) :
    m64RadialCorrect f h p = h p := by
  simp only [m64RadialCorrect, m64RadialLowerFold_eq_self hp, sub_self, zero_add]

theorem m64RadialCorrect_upper {E : Type*} [AddCommGroup E]
    (f h : LoopPlane → E) {p : LoopPlane} (hp : 0 ≤ p 1) :
    m64RadialCorrect f h p = f p - f (m60PlaneReflection p) + h p := by
  rw [m64RadialCorrect, m64RadialLowerFold_eq_reflection hp]

theorem m64RadialCorrect_continuous
    {E : Type*} [NormedAddCommGroup E] {f h : LoopPlane → E}
    (hf : Continuous f) (hh : Continuous h) : Continuous (m64RadialCorrect f h) :=
  (hf.sub (hf.comp m64RadialLowerFold_lipschitz.continuous)).add hh

theorem m64RadialCorrect_lipschitzOn
    {E : Type*} [NormedAddCommGroup E] {f h : LoopPlane → E}
    {a : LoopPlane} (ha : a 1 = 0) {r : ℝ} {K L : ℝ≥0}
    (hf : LipschitzOnWith K f (closedBall a r))
    (hh : LipschitzOnWith L h (closedBall a r)) :
    LipschitzOnWith (2 * K + L) (m64RadialCorrect f h) (closedBall a r) := by
  have hfold := hf.comp m64RadialLowerFold_lipschitz.lipschitzOnWith
    (fun _ hp => m64RadialLowerFold_mem_closedBall ha hp)
  simpa +instances only [mul_one, two_mul, m64RadialCorrect, Function.comp_def] using!
    (hf.sub hfold).add hh

theorem m64RadialCorrect_preserves_sphere
    {E : Type*} [AddCommGroup E] {f h : LoopPlane → E}
    {a : LoopPlane} (ha : a 1 = 0) {r : ℝ}
    (hlower : ∀ p ∈ sphere a r, p 1 ≤ 0 → f p = h p)
    (hsym : ∀ p, h (m60PlaneReflection p) = h p) :
    EqOn (m64RadialCorrect f h) f (sphere a r) := by
  intro p hp
  by_cases hy : p 1 ≤ 0
  · exact (m64RadialCorrect_lower f h hy).trans (hlower p hp hy).symm
  · rw [m64RadialCorrect_upper f h (le_of_not_ge hy)]
    have hRp : m60PlaneReflection p ∈ sphere a r := by
      rw [mem_sphere, ← m64PlaneReflection_fixed ha, m60PlaneReflection.dist_map]
      exact hp
    have hRy : m60PlaneReflection p 1 ≤ 0 := by
      simpa only [m60PlaneReflection_apply, show (1 : Fin 2) ≠ 0 from by decide, if_false]
        using neg_nonpos.mpr (le_of_not_ge hy)
    rw [hlower _ hRp hRy, hsym]
    exact sub_add_cancel _ _

theorem m64RadialCorrect_range_bound
    {E : Type*} [NormedAddCommGroup E] {f h : LoopPlane → E}
    {a : LoopPlane} (ha : a 1 = 0) {r R : ℝ} {z : E}
    (hf : ∀ p ∈ closedBall a r, ‖f p - z‖ ≤ R)
    (hh : ∀ p ∈ closedBall a r, ‖h p - z‖ ≤ R)
    {p : LoopPlane} (hp : p ∈ closedBall a r) :
    ‖m64RadialCorrect f h p - z‖ ≤ 3 * R := by
  have heq : m64RadialCorrect f h p - z =
      (f p - z) - (f (m64RadialLowerFold p) - z) + (h p - z) := by
    simp only [m64RadialCorrect]
    abel
  rw [heq]
  exact (norm_add_le _ _).trans (by
    have hsub := norm_sub_le (f p - z) (f (m64RadialLowerFold p) - z)
    have h0 := hf p hp
    have h1 := hf _ (m64RadialLowerFold_mem_closedBall ha hp)
    have h2 := hh p hp
    linarith)

end PoincareConjecture
