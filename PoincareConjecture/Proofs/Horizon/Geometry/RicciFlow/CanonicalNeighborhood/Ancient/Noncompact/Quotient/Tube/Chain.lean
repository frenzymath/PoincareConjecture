import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Quotient.Tube.Necks
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Quotient.Cap.Topology
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Quotient.Bounds.Distance










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M27TwistedSphereLineFlowCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}
  (C : M27TwistedSphereLineFlowCertificate K)
  {t epsilon : ℝ} (ht : t ≤ 0) (hε : 0 < epsilon) (hhalf : epsilon < 1 / 2)
  (q : UnitTwoSphere)
  (a : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere)
  (ha : ∀ (x : UnitTwoSphere) (v w : TangentSpace (𝓡 2) x),
    (K.flow.connection t).scalarCurvature (C.cover (q, 0)) *
      (C.sphere.metric t).inner (a x)
        (mfderiv (𝓡 2) (𝓡 2) a x v) (mfderiv (𝓡 2) (𝓡 2) a x w) =
          2 * (Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric 2).inner x v w)

private theorem endNeck_mem_carrier_iff (i : ℤ) (hi : 0 ≤ i) (p : UnitTwoSphere × ℝ) :
    C.cover p ∈ (C.endNeck ht hε hhalf q a ha i).terminal_neck.carrier ↔
      ((i : ℝ) + 1) * C.neckSpacing (t := t) (epsilon := epsilon) q < |p.2| ∧
      |p.2| < ((i : ℝ) + 3) * C.neckSpacing (t := t) (epsilon := epsilon) q := by
  rw [C.endNeck_carrier ht hε hhalf q a ha i hi]
  apply C.cover_mem_positiveSlab_iff
  have hi' : (0 : ℝ) ≤ i := by exact_mod_cast hi
  exact mul_nonneg (by linarith) (C.neckSpacing_pos ht hε q).le

private theorem endNeck_mem_region_iff (i : ℤ) (hi : 0 ≤ i) {b c : ℝ}
    (hb : -1 ≤ b) (hc : c ≤ 1) (p : UnitTwoSphere × ℝ) :
    C.cover p ∈ (C.endNeck ht hε hhalf q a ha i).terminal_neck.region
        (b * epsilon⁻¹) (c * epsilon⁻¹) ↔
      ((i : ℝ) + 2 + b) * C.neckSpacing (t := t) (epsilon := epsilon) q < |p.2| ∧
      |p.2| < ((i : ℝ) + 2 + c) * C.neckSpacing (t := t) (epsilon := epsilon) q := by
  rw [C.endNeck_region ht hε hhalf q a ha i hi hb hc]
  apply C.cover_mem_positiveSlab_iff
  have hi' : (0 : ℝ) ≤ i := by exact_mod_cast hi
  exact mul_nonneg (by linarith) (C.neckSpacing_pos ht hε q).le

theorem endNeck_adjacent_edist (i : ℤ) (hi : 0 ≤ i) :
    (K.flow.metric t).edist
      (C.endNeck ht hε hhalf q a ha i).terminal_neck.center
      (C.endNeck ht hε hhalf q a ha (i + 1)).terminal_neck.center =
      ENNReal.ofReal (C.neckSpacing (t := t) (epsilon := epsilon) q) := by
  have hi' : (0 : ℝ) ≤ i := by exact_mod_cast hi
  have hL := C.neckSpacing_pos ht hε q
  rw [C.endNeck_center ht hε hhalf q a ha i hi,
    C.endNeck_center ht hε hhalf q a ha (i + 1) (by omega),
    C.edist_cover_line_eq ht q (by positivity) (by positivity)]
  congr 1
  rw [Int.cast_add, Int.cast_one]
  have hdiff : ((i : ℝ) + 2) * C.neckSpacing (t := t) (epsilon := epsilon) q -
      ((i : ℝ) + 1 + 2) * C.neckSpacing (t := t) (epsilon := epsilon) q =
      -C.neckSpacing (t := t) (epsilon := epsilon) q := by ring
  rw [hdiff, abs_neg, abs_of_pos hL]

noncomputable def balancedEndChain : BalancedNeckChain (K.flow.metric t) epsilon := by
  let L := C.neckSpacing (t := t) (epsilon := epsilon) q
  let N := fun i => (C.endNeck ht hε hhalf q a ha i).terminal_neck
  have hL : 0 < L := C.neckSpacing_pos ht hε q
  have hmem (i : ℤ) (hi : 0 ≤ i) (p : UnitTwoSphere × ℝ) :
      C.cover p ∈ (N i).carrier ↔ ((i : ℝ) + 1) * L < |p.2| ∧ |p.2| < ((i : ℝ) + 3) * L :=
    C.endNeck_mem_carrier_iff ht hε hhalf q a ha i hi p
  have hregion (i : ℤ) (hi : 0 ≤ i) {b c : ℝ} (hb : -1 ≤ b) (hc : c ≤ 1)
      (p : UnitTwoSphere × ℝ) :
      C.cover p ∈ (N i).region (b * epsilon⁻¹) (c * epsilon⁻¹) ↔
        ((i : ℝ) + 2 + b) * L < |p.2| ∧ |p.2| < ((i : ℝ) + 2 + c) * L :=
    C.endNeck_mem_region_iff ht hε hhalf q a ha i hi hb hc p
  have hpquarter (i : ℤ) (hi : 0 ≤ i) (p : UnitTwoSphere × ℝ) :
      C.cover p ∈ (N i).region (epsilon⁻¹ / 2) epsilon⁻¹ ↔
        ((i : ℝ) + 2 + 1 / 2) * L < |p.2| ∧ |p.2| < ((i : ℝ) + 3) * L := by
    simpa only [show (1 / 2 : ℝ) * epsilon⁻¹ = epsilon⁻¹ / 2 by ring, one_mul,
      show (i : ℝ) + 2 + 1 = (i : ℝ) + 3 by ring] using
      hregion i hi (b := 1 / 2) (c := 1) (by norm_num) (by norm_num) p
  have hnquarter (i : ℤ) (hi : 0 ≤ i) (p : UnitTwoSphere × ℝ) :
      C.cover p ∈ (N i).region (-epsilon⁻¹) (-epsilon⁻¹ / 2) ↔
        ((i : ℝ) + 1) * L < |p.2| ∧ |p.2| < ((i : ℝ) + 2 - 1 / 2) * L := by
    simpa only [show (-1 / 2 : ℝ) * epsilon⁻¹ = -epsilon⁻¹ / 2 by ring, neg_one_mul,
      show (i : ℝ) + 2 + -1 = (i : ℝ) + 1 by ring,
      show (i : ℝ) + 2 + -1 / 2 = (i : ℝ) + 2 - 1 / 2 by ring] using
      hregion i hi (b := -1) (c := -1 / 2) (by norm_num) (by norm_num) p
  have hpwide (i : ℤ) (hi : 0 ≤ i) (p : UnitTwoSphere × ℝ) :
      C.cover p ∈ (N i).region (-epsilon⁻¹ / 2) epsilon⁻¹ ↔
        ((i : ℝ) + 2 - 1 / 2) * L < |p.2| ∧ |p.2| < ((i : ℝ) + 3) * L := by
    simpa only [show (-1 / 2 : ℝ) * epsilon⁻¹ = -epsilon⁻¹ / 2 by ring, one_mul,
      show (i : ℝ) + 2 + 1 = (i : ℝ) + 3 by ring,
      show (i : ℝ) + 2 + -1 / 2 = (i : ℝ) + 2 - 1 / 2 by ring] using
      hregion i hi (b := -1 / 2) (c := 1) (by norm_num) (by norm_num) p
  have hnwide (i : ℤ) (hi : 0 ≤ i) (p : UnitTwoSphere × ℝ) :
      C.cover p ∈ (N i).region (-epsilon⁻¹) (epsilon⁻¹ / 2) ↔
        ((i : ℝ) + 1) * L < |p.2| ∧ |p.2| < ((i : ℝ) + 2 + 1 / 2) * L := by
    simpa only [show (1 / 2 : ℝ) * epsilon⁻¹ = epsilon⁻¹ / 2 by ring, neg_one_mul,
      show (i : ℝ) + 2 + -1 = (i : ℝ) + 1 by ring] using
      hregion i hi (b := -1) (c := 1 / 2) (by norm_num) (by norm_num) p
  refine {
    shape := .forward 0
    neck := N
    source_necks := range N
    selected := ?_
    active_nonempty := ⟨0, by change (0 : ℤ) ≤ 0; exact le_rfl⟩
    epsilon_eq := fun _ _ => rfl
    centers_distinct := ?_
    adjacent_overlap := ?_
    overlap_contains_quarters := ?_
    overlap_within_three_quarters := ?_
    later_disjoint_negative_end := ?_
    balanced_center_distance := ?_ }
  · intro i hi
    refine ⟨N i, ⟨i, rfl⟩, rfl, rfl, rfl, rfl, rfl, 1, Or.inl rfl, ?_⟩
    intro z hz
    simp
  · intro i hi j hj hij heq
    change 0 ≤ i at hi
    change 0 ≤ j at hj
    change (C.endNeck ht hε hhalf q a ha i).terminal_neck.center =
      (C.endNeck ht hε hhalf q a ha j).terminal_neck.center at heq
    rw [C.endNeck_center ht hε hhalf q a ha i hi,
      C.endNeck_center ht hε hhalf q a ha j hj] at heq
    have hi' : (0 : ℝ) ≤ i := by exact_mod_cast hi
    have hj' : (0 : ℝ) ≤ j := by exact_mod_cast hj
    have hheight := congrArg C.height heq
    simp only [C.height_cover] at hheight
    change |((i : ℝ) + 2) * L| = |((j : ℝ) + 2) * L| at hheight
    rw [abs_of_nonneg (by positivity : 0 ≤ ((i : ℝ) + 2) * L),
      abs_of_nonneg (by positivity : 0 ≤ ((j : ℝ) + 2) * L)] at hheight
    apply hij
    have heq' : (i : ℝ) = j := by nlinarith
    exact_mod_cast heq'
  · intro i hi hi1
    change 0 ≤ i at hi
    change 0 ≤ i + 1 at hi1
    have hi' : (0 : ℝ) ≤ i := by exact_mod_cast hi
    refine ⟨C.cover (q, ((i : ℝ) + 5 / 2) * L), ?_, ?_⟩
    · rw [hmem i hi, abs_of_nonneg (by positivity : 0 ≤ ((i : ℝ) + 5 / 2) * L)]
      constructor <;> nlinarith
    · rw [hmem (i + 1) hi1, abs_of_nonneg (by positivity : 0 ≤ ((i : ℝ) + 5 / 2) * L),
        Int.cast_add, Int.cast_one]
      constructor <;> nlinarith
  · intro i hi hi1
    change 0 ≤ i at hi
    change 0 ≤ i + 1 at hi1
    constructor
    · intro x hx
      obtain ⟨p, rfl⟩ := C.cover_surjective x
      rw [hpquarter i hi] at hx
      rw [hmem (i + 1) hi1, Int.cast_add, Int.cast_one]
      constructor <;> nlinarith [hx.1, hx.2]
    · intro x hx
      obtain ⟨p, rfl⟩ := C.cover_surjective x
      rw [hnquarter (i + 1) hi1, Int.cast_add, Int.cast_one] at hx
      rw [hmem i hi]
      constructor <;> nlinarith [hx.1, hx.2]
  · intro i hi hi1 x hx
    change 0 ≤ i at hi
    change 0 ≤ i + 1 at hi1
    obtain ⟨p, rfl⟩ := C.cover_surjective x
    rcases hx with ⟨hx, hy⟩
    rw [hmem i hi] at hx
    rw [hmem (i + 1) hi1, Int.cast_add, Int.cast_one] at hy
    rw [mem_inter_iff, hpwide i hi, hnwide (i + 1) hi1, Int.cast_add, Int.cast_one]
    constructor <;> constructor <;> nlinarith [hx.1, hx.2, hy.1, hy.2]
  · intro i hi j hj hij
    change 0 ≤ i at hi
    change 0 ≤ j at hj
    refine ⟨-epsilon⁻¹ / 2, ⟨by linarith [inv_pos.mpr hε], by linarith [inv_pos.mpr hε]⟩, ?_⟩
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨p, rfl⟩ := C.cover_surjective x
    rw [hmem j hj] at hx
    rw [hnquarter i hi] at hy
    have hij' : (i : ℝ) + 1 ≤ j := by
      have hijInt : i + 1 ≤ j := by omega
      exact_mod_cast hijInt
    nlinarith [hx.1, hy.2]
  · intro i hi hi1
    change 0 ≤ i at hi
    have hd := C.endNeck_adjacent_edist ht hε hhalf q a ha i hi
    change (K.flow.metric t).edist (N i).center (N (i + 1)).center = ENNReal.ofReal L at hd
    rw [hd]
    have hscale : (N i).scale * epsilon⁻¹ = L := C.endNeck_scale_mul_epsilon_inv ht hε hhalf q a ha i
    rw [mul_assoc, hscale, mul_assoc, hscale]
    constructor <;> apply ENNReal.ofReal_le_ofReal <;> nlinarith

theorem balancedEndChain_union :
    (⋃ i : {i // i ∈ (C.balancedEndChain ht hε hhalf q a ha).shape.active},
      ((C.balancedEndChain ht hε hhalf q a ha).neck i.1).carrier) =
      (C.slabCore (C.neckSpacing (t := t) (epsilon := epsilon) q))ᶜ := by
  let L := C.neckSpacing (t := t) (epsilon := epsilon) q
  have hL : 0 < L := C.neckSpacing_pos ht hε q
  change (⋃ i : {i : ℤ // 0 ≤ i},
    (C.endNeck ht hε hhalf q a ha i.1).terminal_neck.carrier) = (C.slabCore L)ᶜ
  ext x
  obtain ⟨p, rfl⟩ := C.cover_surjective x
  simp only [mem_iUnion, mem_compl_iff, C.cover_mem_slabCore_iff, not_le]
  constructor
  · rintro ⟨i, hi⟩
    have hh := (C.endNeck_mem_carrier_iff ht hε hhalf q a ha i.1 i.2 p).mp hi
    change ((i.1 : ℝ) + 1) * L < |p.2| ∧ |p.2| < ((i.1 : ℝ) + 3) * L at hh
    have hi' : (0 : ℝ) ≤ i.1 := by exact_mod_cast i.2
    nlinarith [hh.1]
  · intro hp
    let i : ℤ := ⌈|p.2| / L⌉ - 2
    have hi : 0 ≤ i := by
      have hceil : (1 : ℤ) < ⌈|p.2| / L⌉ := Int.lt_ceil.mpr
        ((lt_div_iff₀ hL).mpr (by simpa using hp))
      dsimp [i]
      omega
    refine ⟨⟨i, hi⟩, (C.endNeck_mem_carrier_iff ht hε hhalf q a ha i hi p).mpr ?_⟩
    change ((i : ℝ) + 1) * L < |p.2| ∧ |p.2| < ((i : ℝ) + 3) * L
    constructor
    · apply (lt_div_iff₀ hL).mp
      dsimp [i]
      push_cast
      linarith [Int.ceil_lt_add_one (|p.2| / L)]
    · apply (div_lt_iff₀ hL).mp
      dsimp [i]
      push_cast
      linarith [Int.le_ceil (|p.2| / L)]

end PoincareConjecture.M27TwistedSphereLineFlowCertificate
