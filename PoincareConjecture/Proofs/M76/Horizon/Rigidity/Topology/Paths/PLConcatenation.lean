import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PolyhedralPLClosedUnion
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLDiskExtension
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervals
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition
import Mathlib.Topology.Path

set_option autoImplicit false
open Set

namespace Geometry

variable {X V ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

noncomputable def intervalConcatenation (f g : ℝ → X) (t : ℝ) : X :=
  if t ≤ 1 / 2 then f (2 * t) else g (2 * t - 1)

theorem PolyhedralPLInCharts.interval_concatenation
    {e : ι → OpenPartialHomeomorph X V} {f g : ℝ → X}
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V)
    (hf : PolyhedralPLInCharts e f (Icc (0 : ℝ) 1))
    (hg : PolyhedralPLInCharts e g (Icc (0 : ℝ) 1)) (hfg : f 1 = g 0) :
    PolyhedralPLInCharts e (intervalConcatenation f g) (Icc (0 : ℝ) 1) := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (show (0 : ℝ) < 1 / 2 by norm_num)
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨L, hL, hLs, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (show (1 / 2 : ℝ) < 1 by norm_num)
  let A : ℝ →ᴬ[ℝ] ℝ := (2 : ℝ) • ContinuousAffineMap.id ℝ ℝ
  let C : ℝ →ᴬ[ℝ] ℝ := (2 : ℝ) • ContinuousAffineMap.id ℝ ℝ - ContinuousAffineMap.const ℝ ℝ 1
  have hA : MapsTo A K.space (Icc (0 : ℝ) 1) := by
    intro x hx
    have hx' := hKs.subset hx
    change 0 ≤ 2 * x ∧ 2 * x ≤ 1
    constructor <;> linarith [hx'.1, hx'.2]
  have hC : MapsTo C L.space (Icc (0 : ℝ) 1) := by
    intro x hx
    have hx' := hLs.subset hx
    change 0 ≤ 2 * x - 1 ∧ 2 * x - 1 ≤ 1
    constructor <;> linarith [hx'.1, hx'.2]
  have hleft : PolyhedralPLInCharts e (intervalConcatenation f g) K.space := by
    apply (hf.comp_finitePiecewiseAffineOn K hK
      (show FinitePiecewiseAffineOn A K.space from ⟨K, hK, rfl, K.affineOnFaces_affine A⟩) hA).congr
    intro x hx
    have hx' := hKs.subset hx
    change f (2 * x) = if x ≤ 1 / 2 then f (2 * x) else g (2 * x - 1)
    rw [if_pos hx'.2]
  have hright : PolyhedralPLInCharts e (intervalConcatenation f g) L.space := by
    apply (hg.comp_finitePiecewiseAffineOn L hL
      (show FinitePiecewiseAffineOn C L.space from ⟨L, hL, rfl, L.affineOnFaces_affine C⟩) hC).congr
    intro x hx
    have hx' := hLs.subset hx
    change g (2 * x - 1) = if x ≤ 1 / 2 then f (2 * x) else g (2 * x - 1)
    by_cases hxhalf : x ≤ 1 / 2
    · have heq : x = 1 / 2 := le_antisymm hxhalf hx'.1
      subst x
      simpa using hfg.symm
    · rw [if_neg hxhalf]
  have hwhole := PolyhedralPLInCharts.union_of_finite hcompat K L hK hL hleft hright
  rw [hKs, hLs, Icc_union_Icc_eq_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1)] at hwhole
  exact hwhole

theorem intervalConcatenation_eq_path_trans
    {x y z : X} (a : Path x y) (b : Path y z) {f g : ℝ → X}
    (hf : ∀ t : unitInterval, f t = a t) (hg : ∀ t : unitInterval, g t = b t)
    (t : unitInterval) : intervalConcatenation f g t = a.trans b t := by
  rw [Path.trans_apply]
  unfold intervalConcatenation
  split_ifs with ht
  · exact hf ⟨2 * (t : ℝ), by constructor <;> linarith [t.property.1, t.property.2]⟩
  · exact hg ⟨2 * (t : ℝ) - 1, by constructor <;> linarith [t.property.1, t.property.2]⟩

end Geometry
