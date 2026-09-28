import PoincareConjecture.Proofs.M76.Mathlib.FiniteAffineHalfspaceGeometry
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallTopology
import PoincareConjecture.Proofs.M76.Mathlib.PlanarSegmentHeight

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V" => (ℝ × ℝ)

private theorem exists_returning_support_slope
    (K : SimplicialComplex ℝ V) (hK : K.faces.Finite) {a b : V}
    (hab : a.1 < b.1) (hup : ∀ x ∈ K.space, 0 ≤ x.2)
    (hzero : ∀ x ∈ K.space, x.2 = 0 → x = a ∨ x = b) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K.space,
      a.1 - x.1 ≤ C * x.2 ∧ x.1 - b.1 ≤ C * x.2 := by
  classical
  have hv : K.vertices.Finite := hK.preimage Finset.singleton_injective.injOn
  let r : V → ℝ := fun x => (|a.1 - x.1| + |x.1 - b.1|) / x.2
  obtain ⟨R, hR⟩ := (hv.image r).bddAbove
  let C := max R 0 + 1
  have hC : 0 < C := by dsimp [C]; linarith [le_max_right R 0]
  have hverts (x : V) (hx : x ∈ K.vertices) :
      a.1 - x.1 ≤ C * x.2 ∧ x.1 - b.1 ≤ C * x.2 := by
    have hxK := K.vertices_subset_space hx
    by_cases hx0 : x.2 = 0
    · rcases hzero x hxK hx0 with rfl | rfl <;> simp only [hx0, mul_zero] <;>
        constructor <;> linarith
    · have hxpos : 0 < x.2 := lt_of_le_of_ne (hup x hxK) (Ne.symm hx0)
      have hr : r x ≤ R := hR (mem_image_of_mem r hx)
      have hbound : |a.1 - x.1| + |x.1 - b.1| < C * x.2 := by
        apply (div_lt_iff₀ hxpos).mp
        exact hr.trans_lt (by dsimp [C]; linarith [le_max_left R 0])
      constructor <;> linarith [le_abs_self (a.1 - x.1),
        le_abs_self (x.1 - b.1), abs_nonneg (a.1 - x.1), abs_nonneg (x.1 - b.1)]
  let l : V →ᵃ[ℝ] ℝ := AffineMap.const ℝ V a.1 -
    (LinearMap.fst ℝ ℝ ℝ).toAffineMap - C • (LinearMap.snd ℝ ℝ ℝ).toAffineMap
  let r' : V →ᵃ[ℝ] ℝ := (LinearMap.fst ℝ ℝ ℝ).toAffineMap -
    AffineMap.const ℝ V b.1 - C • (LinearMap.snd ℝ ℝ ℝ).toAffineMap
  have hcv : Convex ℝ {x : V | l x ≤ 0 ∧ r' x ≤ 0} :=
    ((convex_Iic (0 : ℝ)).affine_preimage l).inter
      ((convex_Iic (0 : ℝ)).affine_preimage r')
  refine ⟨C, hC, ?_⟩
  intro x hx
  obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
  have hh : l x ≤ 0 ∧ r' x ≤ 0 := convexHull_min (fun y hy => by
    have h := hverts y (K.face_subset_vertices hs hy)
    change a.1 - y.1 - C * y.2 ≤ 0 ∧ y.1 - b.1 - C * y.2 ≤ 0
    constructor <;> linarith) hcv hxs
  change a.1 - x.1 - C * x.2 ≤ 0 ∧ x.1 - b.1 - C * x.2 ≤ 0 at hh
  constructor <;> linarith

theorem exists_convex_proper_arc_pair_disk {W : Set V} {a b : V}
    (hW : IsFinitePLBallPair ℝ W {a, b}) (hab : a.1 < b.1)
    (ha : a.2 = 0) (hb : b.2 = 0)
    (hup : ∀ x ∈ W, 0 ≤ x.2)
    (hzero : W ∩ {x : V | x.2 = 0} = {a, b}) :
    ∃ D : Set V, IsCompact D ∧ Convex ℝ D ∧
      IsFinitePLBallPair V D (frontier D) ∧
      a ∈ frontier D ∧ b ∈ frontier D ∧
      W ⊆ D ∧ segment ℝ a b ⊆ D ∧
      W \ {a, b} ⊆ interior D ∧ segment ℝ a b \ {a, b} ⊆ interior D ∧
      D ∩ {x : V | x.2 = 0} = segment ℝ a b := by
  classical
  have hcopy := hW
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hcopy
  obtain ⟨c, hc, hbound⟩ := exists_returning_support_slope K hK hab
    (fun x hx => hup x (hKs ▸ hx))
    (fun x hx hx0 => hzero.subset ⟨hKs ▸ hx, hx0⟩)
  have hbnd (x : V) (hx : x ∈ W) :
      a.1 - x.1 ≤ c * x.2 ∧ x.1 - b.1 ≤ c * x.2 := hbound x (hKs.symm ▸ hx)
  obtain ⟨r, hr⟩ := (hW.isCompact.image continuous_snd).bddAbove
  let R := max r 0 + 1
  have hR : 0 < R := by dsimp [R]; linarith [le_max_right r 0]
  have htop (x : V) (hx : x ∈ W) : x.2 < R :=
    (hr (mem_image_of_mem Prod.snd hx)).trans_lt
      (by dsimp [R]; linarith [le_max_left r 0])
  let C := c + 1
  have hC : 0 < C := by dsimp [C]; linarith
  let A : Fin 3 → V →ᵃ[ℝ] ℝ := ![
    AffineMap.const ℝ V a.1 - (LinearMap.fst ℝ ℝ ℝ).toAffineMap -
      C • (LinearMap.snd ℝ ℝ ℝ).toAffineMap,
    (LinearMap.fst ℝ ℝ ℝ).toAffineMap - AffineMap.const ℝ V b.1 -
      C • (LinearMap.snd ℝ ℝ ℝ).toAffineMap,
    (LinearMap.snd ℝ ℝ ℝ).toAffineMap - AffineMap.const ℝ V R]
  have hA0 (x : V) : A 0 x = a.1 - x.1 - C * x.2 := rfl
  have hA1 (x : V) : A 1 x = x.1 - b.1 - C * x.2 := rfl
  have hA2 (x : V) : A 2 x = x.2 - R := rfl
  have hA (i : Fin 3) : (A i).linear ≠ 0 := by
    intro hz
    fin_cases i
    · have hh := congrArg (fun f : V →ₗ[ℝ] ℝ => f (1, 0)) hz
      norm_num [A] at hh
    · have hh := congrArg (fun f : V →ₗ[ℝ] ℝ => f (1, 0)) hz
      norm_num [A] at hh
    · have hh := congrArg (fun f : V →ₗ[ℝ] ℝ => f (0, 1)) hz
      norm_num [A] at hh
  let D := {x : V | ∀ i, A i x ≤ 0}
  have hmem (x : V) : x ∈ D ↔
      a.1 - x.1 ≤ C * x.2 ∧ x.1 - b.1 ≤ C * x.2 ∧ x.2 ≤ R := by
    constructor
    · intro hx
      have h0 := hx 0
      have h1 := hx 1
      have h2 := hx 2
      rw [hA0] at h0
      rw [hA1] at h1
      rw [hA2] at h2
      exact ⟨by linarith, by linarith, by linarith⟩
    · rintro ⟨h0, h1, h2⟩ i
      fin_cases i
      · change a.1 - x.1 - C * x.2 ≤ 0; linarith
      · change x.1 - b.1 - C * x.2 ≤ 0; linarith
      · change x.2 - R ≤ 0; linarith
  have hint : interior D = {x : V | ∀ i, A i x < 0} :=
    interior_finite_affine_halfspaces A hA
  have hstrict (x : V) (hl : a.1 - x.1 < C * x.2)
      (hr' : x.1 - b.1 < C * x.2) (ht : x.2 < R) : x ∈ interior D := by
    rw [hint]
    intro i
    fin_cases i
    · change a.1 - x.1 - C * x.2 < 0; linarith
    · change x.1 - b.1 - C * x.2 < 0; linarith
    · change x.2 - R < 0; linarith
  have hclosed : IsClosed D := by
    simp only [D, ofPred_forall]
    exact isClosed_iInter fun i =>
      isClosed_le (A i).continuous_of_finiteDimensional continuous_const
  have hcompact : IsCompact D := by
    apply (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hclosed
      (s := Icc (a.1 - C * R) (b.1 + C * R) ×ˢ Icc ((a.1 - b.1) / (2 * C)) R)
    intro x hx
    obtain ⟨hl, hr', ht⟩ := (hmem x).mp hx
    have hy : C * x.2 ≤ C * R := mul_le_mul_of_nonneg_left ht hC.le
    refine ⟨⟨by linarith, by linarith⟩, ?_, ht⟩
    apply (div_le_iff₀ (by positivity : 0 < 2 * C)).mpr
    nlinarith
  have hconvex : Convex ℝ D := by
    change Convex ℝ {x : V | ∀ i, A i x ≤ 0}
    simp only [ofPred_forall]
    exact convex_iInter fun i => (convex_Iic (0 : ℝ)).affine_preimage (A i)
  have hmiddle : ((a.1 + b.1) / 2, 0) ∈ interior D := by
    apply hstrict <;> dsimp <;> linarith
  have hball : IsFinitePLBallPair V D (frontier D) := by
    apply isFinitePLBallPair_of_affine_halfspaces hcompact (Finset.univ.image A)
      _ ⟨_, hmiddle⟩
    ext x
    simp only [D, mem_ofPred_eq, Finset.forall_mem_image, Finset.mem_univ, true_implies]
  have haD : a ∈ D := by
    rw [hmem, ha, mul_zero]
    exact ⟨by linarith, by linarith, by linarith⟩
  have hbD : b ∈ D := by
    rw [hmem, hb, mul_zero]
    exact ⟨by linarith, by linarith, by linarith⟩
  have haF : a ∈ frontier D := by
    rw [frontier, hclosed.closure_eq]
    refine ⟨haD, ?_⟩
    intro hi
    have hh := (hint.subset hi) 0
    rw [hA0, ha] at hh
    simp at hh
  have hbF : b ∈ frontier D := by
    rw [frontier, hclosed.closure_eq]
    refine ⟨hbD, ?_⟩
    intro hi
    have hh := (hint.subset hi) 1
    rw [hA1, hb] at hh
    simp at hh
  have hWin : W \ {a, b} ⊆ interior D := by
    rintro x ⟨hx, hn⟩
    have hxpos : 0 < x.2 := lt_of_le_of_ne (hup x hx) (by
      intro hh
      exact hn (hzero.subset ⟨hx, hh.symm⟩))
    have hh := hbnd x hx
    apply hstrict x _ _ (htop x hx) <;> dsimp [C] <;> nlinarith
  have hWD : W ⊆ D := by
    intro x hx
    by_cases he : x ∈ ({a, b} : Set V)
    · rcases he with rfl | rfl
      · exact haD
      · exact hbD
    · exact interior_subset (hWin ⟨hx, he⟩)
  have hseg : segment ℝ a b ⊆ D := hconvex.segment_subset haD hbD
  have hseg0 (x : V) (hx : x ∈ segment ℝ a b) : x.2 = 0 := by
    rw [((PlanarSegment.mem_segment_iff hab.ne).mp hx).2]
    simp [PlanarSegment.height, ha, hb]
  refine ⟨D, hcompact, hconvex, hball, haF, hbF, hWD, hseg, hWin, ?_, ?_⟩
  · rintro x ⟨hx, hn⟩
    have hxcoord := (PlanarSegment.mem_segment_iff hab.ne).mp hx
    have hx0 := hseg0 x hx
    rw [uIcc_of_le hab.le] at hxcoord
    have hxa : a.1 < x.1 := lt_of_le_of_ne hxcoord.1.1 (by
      intro hh
      exact hn (Or.inl (Prod.ext hh.symm (hx0.trans ha.symm))))
    have hxb : x.1 < b.1 := lt_of_le_of_ne hxcoord.1.2 (by
      intro hh
      exact hn (Or.inr (Prod.ext hh (hx0.trans hb.symm))))
    apply hstrict <;> simp only [hx0, mul_zero] <;> linarith
  · ext x
    constructor
    · rintro ⟨hx, hx0⟩
      change x.2 = 0 at hx0
      have hh := (hmem x).mp hx
      apply (PlanarSegment.mem_segment_iff hab.ne).mpr
      rw [uIcc_of_le hab.le]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simpa only [hx0, mul_zero, sub_nonpos] using hh.1
      · simpa only [hx0, mul_zero, sub_nonpos] using hh.2.1
      · simp [PlanarSegment.height, ha, hb, hx0]
    · intro hx
      exact ⟨hseg hx, hseg0 x hx⟩

end PoincareConjecture.M76
