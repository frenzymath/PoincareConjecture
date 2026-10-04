import PoincareLib.Topology.Manifold.Schoenflies.Plane.Polygon.SimplePolygon
import PoincareLib.Topology.Manifold.Schoenflies.Plane.Rounding.RoundedCorner
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Periodic

/-!
# The actual cyclic parameter of a finite polygon

Sections 3-4 of the P2 planar-transfer skeleton. Euclidean integer
indices give the actual periodic affine curve of a finite polygon.
Its fixed local corner formula proves joint continuity. Simple edge
incidence proves injection on one half-open period, and its range is
exactly the existing polygon boundary.
See `smale/derivations/2026-09-22-polygonal-parameter.md`.
-/

set_option autoImplicit false

open Set Function Filter
open scoped Topology

namespace Poincare.Manifold.Schoenflies.Plane

/-- The cyclic vertex index from Euclidean integer remainder, including
negative indices; P2 skeleton, section 3, actual polygon rounding. -/
def polygonIntegerIndex (n : ℕ) [NeZero n] (j : ℤ) : Fin n :=
  ⟨(j % (n : ℤ)).toNat, (Int.toNat_lt (Int.emod_nonneg _ (by
    exact_mod_cast NeZero.ne n))).mpr (Int.emod_lt_of_pos _ (by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)))⟩

variable {n : ℕ} [NeZero n]

/-- A finite vertex keeps its own index; P2 skeleton, section 3. -/
theorem polygonIntegerIndex_nat (i : Fin n) : polygonIntegerIndex n (i.val : ℤ) = i := by
  apply Fin.ext
  change ((i.val : ℤ) % (n : ℤ)).toNat = i.val
  rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast i.isLt)]
  rfl

/-- Adding the vertex count preserves the actual index; P2 skeleton, section 3. -/
theorem polygonIntegerIndex_add_period (j : ℤ) :
    polygonIntegerIndex n (j + n) = polygonIntegerIndex n j := by
  apply Fin.ext
  exact congrArg Int.toNat (Int.add_emod_right j n)

/-- Integer succession agrees with the polygon's cyclic rotation;
P2 skeleton, section 3, including the last-to-first edge. -/
theorem polygonIntegerIndex_succ (j : ℤ) :
    polygonIntegerIndex n (j + 1) = finRotate n (polygonIntegerIndex n j) := by
  rw [finRotate_apply]
  apply Fin.ext
  change ((j + 1) % (n : ℤ)).toNat = ((j % (n : ℤ)).toNat + 1 % n) % n
  apply Int.ofNat_inj.mp
  have hn : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
  simp only [Int.natCast_emod, Int.natCast_add, Int.natCast_one,
    Int.toNat_of_nonneg (Int.emod_nonneg (j + 1) hn),
    Int.toNat_of_nonneg (Int.emod_nonneg j hn)]
  exact Int.add_emod j 1 n

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual affine curve traversing each polygon edge in one unit
of real parameter; P2 skeleton, section 3. -/
noncomputable def polygonLinearParameter (p : Polygon E n) (t : ℝ) : E :=
  let j : ℤ := ⌊t⌋
  p (polygonIntegerIndex n j) + (t - j) •
    (p (polygonIntegerIndex n (j + 1)) - p (polygonIntegerIndex n j))

/-- The affine edge formula holds on the closed unit interval, including
its right endpoint; P2 skeleton, section 3. -/
theorem polygonLinearParameter_eq_edge (p : Polygon E n) (i : ℤ) {t : ℝ}
    (ht : t ∈ Icc (i : ℝ) ((i : ℝ) + 1)) :
    polygonLinearParameter p t = p.edgePath ℝ (polygonIntegerIndex n i) (t - i) := by
  by_cases hlt : t < (i : ℝ) + 1
  · have hf : ⌊t⌋ = i := Int.floor_eq_iff.mpr ⟨ht.1, hlt⟩
    simp only [polygonLinearParameter, hf, Polygon.edgePath,
      AffineMap.lineMap_apply_module', polygonIntegerIndex_succ]
    exact add_comm _ _
  · have heq : t = ((i + 1 : ℤ) : ℝ) := by
      rw [Int.cast_add, Int.cast_one]
      exact le_antisymm ht.2 (le_of_not_gt hlt)
    rw [heq, polygonLinearParameter, Int.floor_intCast]
    simp only [sub_self, zero_smul, add_zero, Int.cast_add, Int.cast_one]
    rw [show (i : ℝ) + 1 - i = 1 by ring]
    simp only [Polygon.edgePath, AffineMap.lineMap_apply_one, polygonIntegerIndex_succ]

/-- The actual polygon curve has the vertex count as an exact period;
P2 skeleton, section 3. -/
theorem periodic_polygonLinearParameter (p : Polygon E n) :
    Periodic (polygonLinearParameter p) (n : ℝ) := by
  intro t
  have hf : ⌊t + (n : ℝ)⌋ = ⌊t⌋ + (n : ℤ) := by
    exact Int.floor_add_intCast t n
  simp only [polygonLinearParameter, hf]
  rw [show ⌊t⌋ + (n : ℤ) + 1 = (⌊t⌋ + 1) + n by omega]
  simp only [polygonIntegerIndex_add_period, Int.cast_add, Int.cast_natCast]
  congr 2
  ring

/-- On an open vertex interval the actual polygon is the absolute-value
corner formula; P2 skeleton, section 3, coherent rounding input. -/
theorem polygonLinearParameter_eq_corner (p : Polygon E n) (i : ℤ) {t : ℝ}
    (ht : t ∈ Ioo ((i : ℝ) - 1) ((i : ℝ) + 1)) :
    polygonLinearParameter p t = roundedCorner abs (p (polygonIntegerIndex n i))
      (p (polygonIntegerIndex n i) - p (polygonIntegerIndex n (i - 1)))
      (p (polygonIntegerIndex n (i + 1)) - p (polygonIntegerIndex n i)) (t - i) := by
  by_cases hti : t < (i : ℝ)
  · have hmem : t ∈ Icc ((i - 1 : ℤ) : ℝ) (((i - 1 : ℤ) : ℝ) + 1) := by
      simp only [Int.cast_sub, Int.cast_one]
      constructor <;> linarith [ht.1]
    rw [polygonLinearParameter_eq_edge p (i - 1) hmem]
    simp only [Polygon.edgePath, AffineMap.lineMap_apply_module',
      ← polygonIntegerIndex_succ, sub_add_cancel, Int.cast_sub, Int.cast_one,
      roundedCorner, abs_of_neg (sub_neg.mpr hti)]
    module
  · have hmem : t ∈ Icc (i : ℝ) ((i : ℝ) + 1) := ⟨le_of_not_gt hti, ht.2.le⟩
    rw [polygonLinearParameter_eq_edge p i hmem]
    simp only [Polygon.edgePath, AffineMap.lineMap_apply_module',
      ← polygonIntegerIndex_succ, roundedCorner, abs_of_nonneg (sub_nonneg.mpr hmem.1)]
    module

/-- Continuous vertex families give joint continuity of the actual
polygon curve, including every vertex; P2 skeleton, section 4. -/
theorem continuous_polygonLinearParameter {Z : Type*} [TopologicalSpace Z]
    {p : Z → Polygon E n} (hp : ∀ i, Continuous (fun z => p z i)) :
    Continuous (fun x : Z × ℝ => polygonLinearParameter (p x.1) x.2) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  let i : ℤ := ⌊x.2⌋
  have hlo : (i : ℝ) ≤ x.2 := Int.floor_le _
  have hhi : x.2 < (i : ℝ) + 1 := Int.lt_floor_add_one _
  have hx : x.2 ∈ Ioo ((i : ℝ) - 1) ((i : ℝ) + 1) := ⟨by linarith, hhi⟩
  have hF : Continuous (fun y : Z × ℝ => roundedCorner abs
      (p y.1 (polygonIntegerIndex n i))
      (p y.1 (polygonIntegerIndex n i) - p y.1 (polygonIntegerIndex n (i - 1)))
      (p y.1 (polygonIntegerIndex n (i + 1)) - p y.1 (polygonIntegerIndex n i))
      (y.2 - i)) := by
    unfold roundedCorner
    have hi : Continuous (fun y : Z × ℝ => p y.1 (polygonIntegerIndex n i)) :=
      (hp (polygonIntegerIndex n i)).comp continuous_fst
    have hm : Continuous (fun y : Z × ℝ => p y.1 (polygonIntegerIndex n (i - 1))) :=
      (hp (polygonIntegerIndex n (i - 1))).comp continuous_fst
    have hn : Continuous (fun y : Z × ℝ => p y.1 (polygonIntegerIndex n (i + 1))) :=
      (hp (polygonIntegerIndex n (i + 1))).comp continuous_fst
    have htime : Continuous (fun y : Z × ℝ => y.2 - (i : ℝ)) :=
      continuous_snd.sub continuous_const
    exact (hi.add (((htime.sub htime.abs).div_const 2).smul (hi.sub hm))).add
      (((htime.add htime.abs).div_const 2).smul (hn.sub hi))
  apply hF.continuousAt.congr_of_eventuallyEq
  have hU : ∀ᶠ y : Z × ℝ in 𝓝 x, y.2 ∈ Ioo ((i : ℝ) - 1) ((i : ℝ) + 1) :=
    continuous_snd.continuousAt (isOpen_Ioo.mem_nhds hx)
  filter_upwards [hU] with y hy
  exact polygonLinearParameter_eq_corner (p y.1) i hy

/-- Simple edge incidence gives injection on one half-open period of
the actual polygon curve; P2 skeleton, section 3. -/
theorem IsSimplePolygon.injOn_polygonLinearParameter {p : Polygon E n}
    (hp : IsSimplePolygon p) : InjOn (polygonLinearParameter p) (Ico 0 (n : ℝ)) := by
  intro s hs t ht heq
  let j : ℤ := ⌊s⌋
  let k : ℤ := ⌊t⌋
  have hjs : (j : ℝ) ≤ s := Int.floor_le _
  have hsj : s < (j : ℝ) + 1 := Int.lt_floor_add_one _
  have hkt : (k : ℝ) ≤ t := Int.floor_le _
  have htk : t < (k : ℝ) + 1 := Int.lt_floor_add_one _
  have hj0 : 0 ≤ j := Int.floor_nonneg.mpr hs.1
  have hk0 : 0 ≤ k := Int.floor_nonneg.mpr ht.1
  have hjn : j < (n : ℤ) := by exact_mod_cast lt_of_le_of_lt hjs hs.2
  have hkn : k < (n : ℤ) := by exact_mod_cast lt_of_le_of_lt hkt ht.2
  have hej := polygonLinearParameter_eq_edge p j ⟨hjs, hsj.le⟩
  have hek := polygonLinearParameter_eq_edge p k ⟨hkt, htk.le⟩
  rw [hej, hek] at heq
  by_cases hidx : polygonIntegerIndex n j = polygonIntegerIndex n k
  · have hvalues := congrArg Fin.val hidx
    change (j % (n : ℤ)).toNat = (k % (n : ℤ)).toNat at hvalues
    rw [Int.emod_eq_of_lt hj0 hjn, Int.emod_eq_of_lt hk0 hkn] at hvalues
    have hjk : j = k := by
      have hv := congrArg (fun a : ℕ => (a : ℤ)) hvalues
      simpa only [Int.toNat_of_nonneg hj0, Int.toNat_of_nonneg hk0] using hv
    rw [hidx] at heq
    have hparam := hp.edgePath_injective (polygonIntegerIndex n k) heq
    rw [hjk] at hparam
    linarith
  · have hsj' : s - (j : ℝ) ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith
    have htk' : t - (k : ℝ) ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith
    have hends := hp.edges_inter (polygonIntegerIndex n j) (polygonIntegerIndex n k)
      hidx ⟨⟨s - j, hsj', rfl⟩, ⟨t - k, htk', heq.symm⟩⟩
    have hleftj : p.edgePath ℝ (polygonIntegerIndex n j) (s - j) =
        p (polygonIntegerIndex n j) := by
      rcases hends.1 with h | h
      · exact h
      · have hparam : s - (j : ℝ) = 1 := hp.edgePath_injective _ (by
          simpa only [Polygon.edgePath, AffineMap.lineMap_apply_one, mem_singleton_iff] using h)
        linarith
    have hleftk : p.edgePath ℝ (polygonIntegerIndex n j) (s - j) =
        p (polygonIntegerIndex n k) := by
      rcases hends.2 with h | h
      · exact h
      · have hparam : t - (k : ℝ) = 1 := hp.edgePath_injective _ (by
          simpa only [Polygon.edgePath, AffineMap.lineMap_apply_one] using heq.symm.trans h)
        linarith
    exact False.elim (hidx (hp.vertices_injective (hleftj.symm.trans hleftk)))

/-- The actual cyclic curve has exactly the polygon's edge-union range;
P2 skeleton, section 3, geometric identification for rounding. -/
theorem range_polygonLinearParameter (p : Polygon E n) :
    range (polygonLinearParameter p) = p.boundary ℝ := by
  apply subset_antisymm
  · rintro _ ⟨t, rfl⟩
    let j : ℤ := ⌊t⌋
    have hlo : (j : ℝ) ≤ t := Int.floor_le _
    have hhi : t < (j : ℝ) + 1 := Int.lt_floor_add_one _
    apply polygon_edgeSet_subset_boundary p (polygonIntegerIndex n j)
    refine ⟨t - j, ⟨by linarith, by linarith⟩, ?_⟩
    exact (polygonLinearParameter_eq_edge p j ⟨hlo, hhi.le⟩).symm
  · intro x hx
    obtain ⟨i, θ, hθ, rfl⟩ := (polygon_mem_boundary_iff p x).mp hx
    refine ⟨(i.val : ℝ) + θ, ?_⟩
    have hm : (i.val : ℝ) + θ ∈ Icc ((i.val : ℤ) : ℝ) (((i.val : ℤ) : ℝ) + 1) := by
      simp only [Int.cast_natCast]
      constructor <;> linarith [hθ.1, hθ.2]
    rw [polygonLinearParameter_eq_edge p (i.val : ℤ) hm, polygonIntegerIndex_nat]
    congr 1
    simp only [Int.cast_natCast]
    ring

end Poincare.Manifold.Schoenflies.Plane
