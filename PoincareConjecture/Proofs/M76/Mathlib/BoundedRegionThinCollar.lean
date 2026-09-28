import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionThinCollarModel
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLDomination

set_option autoImplicit false

open Set Geometry

namespace TriangularRoofModel

theorem exists_thinCollar_avoiding_polyhedron
    (K : SimplicialComplex ℝ ((ℝ × ℝ) × ℝ)) (hK : K.faces.Finite)
    (hKh : K.space ⊆ halfBall 1) (hKd : K.space ∩ disk ⊆ rim) :
    ∃ t : ℝ, t ∈ Ioo 0 1 ∧ K.space ∩ thinCollar t ⊆ rim ∧
      thinCollar t ⊆ halfBall 1 ∧ thinCollar t ∩ cap 1 = rim ∧
      IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (thinCollar t) (cap t ∪ disk) := by
  let a := (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ).toContinuousAffineMap
  have hbase : MapsTo a K.space base := by
    intro p hp
    have hh := hKh hp
    change 0 ≤ (1 : ℝ) * p.2 ∧ (1 : ℝ) * p.2 ≤ roof p.1 at hh
    exact (roof_nonneg_iff p.1).mp (hh.1.trans hh.2)
  have hf : FinitePiecewiseAffineOn (fun p : (ℝ × ℝ) × ℝ => roof p.1) K.space :=
    finitePiecewiseAffineOn_roof.comp
      ⟨K, hK, rfl, K.affineOnFaces_affine a⟩ hbase
  have hg : FinitePiecewiseAffineOn (fun p : (ℝ × ℝ) × ℝ => p.2) K.space :=
    ⟨K, hK, rfl, K.affineOnFaces_affine
      (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).toContinuousAffineMap⟩
  have hgn (p : (ℝ × ℝ) × ℝ) (hp : p ∈ K.space) : 0 ≤ p.2 := by
    have hh := hKh hp
    change 0 ≤ (1 : ℝ) * p.2 ∧ (1 : ℝ) * p.2 ≤ roof p.1 at hh
    simpa only [one_mul] using hh.1
  have hzero (p : (ℝ × ℝ) × ℝ) (hp : p ∈ K.space) (hpzero : p.2 = 0) :
      roof p.1 ≤ 0 := by
    have hpd : p ∈ disk := (mem_disk p).mpr ⟨hbase hp, hpzero⟩
    exact ((mem_rim p).mp (hKd ⟨hp, hpd⟩)).1.le
  obtain ⟨ε, hε, hbound⟩ := hf.exists_small_mul_lt_of_pos hg hgn hzero
  let t := min ε (1 / 2)
  have ht : 0 < t := lt_min hε (by norm_num)
  have htε : t ≤ ε := min_le_left _ _
  have htone : t < 1 := (min_le_right ε (1 / 2)).trans_lt (by norm_num)
  refine ⟨t, ⟨ht, htone⟩, ?_, thinCollar_subset_halfBall ht htone.le,
    thinCollar_inter_cap htone, isFinitePLBallPair_thinCollar ht⟩
  rintro p ⟨hpK, hpt⟩
  change 0 ≤ p.2 ∧ p.2 ≤ t * roof p.1 at hpt
  by_cases hpzero : p.2 = 0
  · exact hKd ⟨hpK, (mem_disk p).mpr ⟨hbase hpK, hpzero⟩⟩
  · have hpos : 0 < p.2 := lt_of_le_of_ne (hgn p hpK) (Ne.symm hpzero)
    exact ((not_lt_of_ge hpt.2) (hbound t ⟨ht.le, htε⟩ p hpK hpos)).elim

end TriangularRoofModel
