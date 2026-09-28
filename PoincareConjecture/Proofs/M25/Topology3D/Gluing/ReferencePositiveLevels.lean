import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedSupport.NativeLevelGeometry
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceHighRegularity

set_option autoImplicit false

open Set
open scoped ContDiff Manifold Matrix

namespace PoincareConjecture.M25.Topology3D

theorem saddle_nested_reference_positive_level_connected_of_roots
    (ws wm : ℝ)
    (hwslo : (1 : ℝ) / 2 < ws) (hwshi : ws < 3 / 4)
    (hwsroot : (2 - 1 / ws) * Real.sqrt (1 - ws ^ 2) = 1 / 32)
    (hwmlo : 0 < wm) (hwmhi : wm < 1 / 2)
    (hwmroot : (2 - 1 / wm) * Real.sqrt (1 - wm ^ 2) = -(1 / 32)) :
    let k : ℝ := 1 - ws ^ 2 + ws - Real.sqrt (1 - ws ^ 2) / 32
    let mu : ℝ := 1 - wm ^ 2 + wm + Real.sqrt (1 - wm ^ 2) / 32
    ∀ d a : ℝ, k < a → a < mu →
      IsConnected ((nestedReferenceBallChart d).boundary ∩
        {y : E3 | (heightCoordinates y).2 = a + d}) := by
  classical
  intro k mu
  have hExist := saddle_nested_reference_positive_level_connected
  dsimp only at hExist
  obtain ⟨ws0, wm0, hwslo0, hwshi0, hwsroot0, hwmlo0, hwmhi0,
    hwmroot0, hConnected⟩ := hExist
  obtain ⟨w, _, hwunique⟩ := exists_unique_nestedReference_saddle_root
  have hseq : ws0 = ws := (hwunique ws0 ⟨hwslo0, hwshi0, hwsroot0⟩).trans
    (hwunique ws ⟨hwslo, hwshi, hwsroot⟩).symm
  subst ws0
  let U : E2 → ℝ := fun v =>
    ‖v‖ ^ 2 + Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32
  let vs : E2 := !₂[-Real.sqrt (1 - ws ^ 2), 0]
  let vm0 : E2 := !₂[Real.sqrt (1 - wm0 ^ 2), 0]
  let vm : E2 := !₂[Real.sqrt (1 - wm ^ 2), 0]
  let qs : UnitTwoSphere := -southSpherePoint (-vs)
  let qm0 : UnitTwoSphere := -southSpherePoint (-vm0)
  let qm : UnitTwoSphere := -southSpherePoint (-vm)
  let H : UnitTwoSphere → ℝ := fun q =>
    (heightCoordinates (nestedReferenceDiffeomorph 0 (q : E3))).2
  have hOld := NestedReferenceLower.reference_high_sphere_regularity
    ws wm0 0 hwslo hwshi hwsroot hwmlo0 hwmhi0 hwmroot0
  have hNew := NestedReferenceLower.reference_high_sphere_regularity
    ws wm 0 hwslo hwshi hwsroot hwmlo hwmhi hwmroot
  dsimp only at hOld hNew
  obtain ⟨_, _, _, hmax0, _, hcoord0, _, hval0, hclass0, _, _⟩ := hOld
  obtain ⟨_, _, hsaddle, _, _, hcoord, hsval, _, hclass, _, _⟩ := hNew
  change 5 / 4 < U vm0 at hmax0
  change U vs < 5 / 4 at hsaddle
  change H qm0 = U vm0 + 0 at hval0
  change H qs = U vs + 0 at hsval
  change heightCoordinates (qm0 : E3) = (vm0, wm0) at hcoord0
  change heightCoordinates (qm : E3) = (vm, wm) at hcoord
  simp only [add_zero] at hval0 hsval
  have hhigh : (17 : ℝ) / 16 < H qm0 - 0 := by
    rw [sub_zero, hval0]
    linarith only [hmax0]
  have hcrit : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) H qm0 = 0 :=
    (hclass0 qm0 hhigh).2.2.2.mpr (Or.inr rfl)
  have hwhich : qm0 = qs ∨ qm0 = qm :=
    (hclass qm0 hhigh).2.2.2.mp hcrit
  have hpoint : qm0 = qm := by
    rcases hwhich with hs | hm
    · have hbad : U vm0 < 5 / 4 := by
        rw [← hval0, hs, hsval]
        exact hsaddle
      linarith only [hmax0, hbad]
    · exact hm
  have hmeq : wm0 = wm := by
    have hh := congrArg (fun q : UnitTwoSphere => (heightCoordinates (q : E3)).2) hpoint
    simpa only [hcoord0, hcoord] using hh
  subst wm0
  change ∀ d a : ℝ, U vs < a → a < U vm →
    IsConnected ((nestedReferenceBallChart d).boundary ∩
      {y : E3 | (heightCoordinates y).2 = a + d}) at hConnected
  have hValue (w s : ℝ) (hw : 0 < w) (hw1 : w < 1) (hs : s ^ 2 = 1) :
      U (!₂[s * Real.sqrt (1 - w ^ 2), 0] : E2) =
        1 - w ^ 2 + w + s * Real.sqrt (1 - w ^ 2) / 32 := by
    have hw2 : 0 ≤ 1 - w ^ 2 := by nlinarith only [hw, hw1]
    have hn : ‖(!₂[s * Real.sqrt (1 - w ^ 2), 0] : E2)‖ ^ 2 = 1 - w ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
      change (s * Real.sqrt (1 - w ^ 2)) ^ 2 + (0 : ℝ) ^ 2 = _
      rw [mul_pow, hs, one_mul, Real.sq_sqrt hw2]
      ring
    change ‖(!₂[s * Real.sqrt (1 - w ^ 2), 0] : E2)‖ ^ 2 +
      Real.sqrt (1 - ‖(!₂[s * Real.sqrt (1 - w ^ 2), 0] : E2)‖ ^ 2) +
        s * Real.sqrt (1 - w ^ 2) / 32 = _
    rw [hn, sub_sub_cancel, Real.sqrt_sq hw.le]
  have hk : U vs = k := by
    simpa only [vs, k, neg_one_mul, neg_div, sub_eq_add_neg] using
      hValue ws (-1) (by linarith only [hwslo])
        (by linarith only [hwshi]) (by norm_num)
  have hmu : U vm = mu := by
    simpa only [vm, mu, one_mul] using
      hValue wm 1 hwmlo (by linarith only [hwmhi]) (by norm_num)
  intro d a hka hamu
  apply hConnected d a
  · simpa only [hk] using hka
  · simpa only [hmu] using hamu

end PoincareConjecture.M25.Topology3D
