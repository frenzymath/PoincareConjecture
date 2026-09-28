import PoincareConjecture.Proofs.M76.Mathlib.RadialFrontierConeBall
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall











set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

local notation "V2" => (Fin 2 → ℝ)
local notation "Q2" => sphere (0 : V2) 1

noncomputable def circleLevelLift : E →ᴬ[ℝ] (E × ℝ) :=
  (ContinuousAffineMap.id ℝ E).prod (ContinuousAffineMap.const ℝ E 1)


def boundaryCircleCone (S : Set E) : Set (E × ℝ) :=
  convexJoin ℝ {0} (circleLevelLift '' S)

omit [FiniteDimensional ℝ E] in
theorem mem_boundaryCircleCone_iff (S : Set E) (x : E × ℝ) :
    x ∈ boundaryCircleCone S ↔ ∃ y ∈ S, ∃ r ∈ Icc (0 : ℝ) 1, x = (r • y, r) := by
  rw [boundaryCircleCone, mem_convexJoin_zero_iff]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, r, hr, rfl⟩
    exact ⟨y, hy, r, hr, by ext <;> simp [circleLevelLift]⟩
  · rintro ⟨y, hy, r, hr, rfl⟩
    refine ⟨circleLevelLift y, mem_image_of_mem _ hy, r, hr, ?_⟩
    ext <;> simp [circleLevelLift]


theorem isFinitePLBallPair_boundaryCircleCone {S : Set E}
    (b : Q2 ≃ₜ S) (hb : b.IsFinitePL) :
    IsFinitePLBallPair V2 (boundaryCircleCone S) (circleLevelLift '' S) := by
  obtain ⟨_, ⟨K, hK, hKs, _⟩, _⟩ := hb.symm
  have hlift : FinitePiecewiseAffineOn (circleLevelLift : E → E × ℝ) S :=
    ⟨K, hK, hKs, K.affineOnFaces_affine circleLevelLift⟩
  obtain ⟨c, hc, _⟩ := hlift.exists_homeomorph_image
    (fun x _ y _ hxy ↦ congrArg Prod.fst hxy)
  let d := c.symm.trans b.symm
  have hd : d.IsFinitePL := hc.symm.trans hb.symm
  have hfront : Q2 = frontier (closedBall (0 : V2) 1) :=
    (frontier_closedBall (0 : V2) one_ne_zero).symm
  have hd' := hd.setCongr rfl hfront
  have hcv : Convex ℝ ((univ : Set E) ×ˢ Iic (1 : ℝ)) := convex_univ.prod (convex_Iic 1)
  have hzero : (0 : E × ℝ) ∈ interior ((univ : Set E) ×ˢ Iic (1 : ℝ)) := by
    simp only [interior_prod_eq, interior_univ, interior_Iic, mem_prod, mem_univ,
      mem_Iio, true_and]
    norm_num
  have hboundary : circleLevelLift '' S ⊆ frontier ((univ : Set E) ×ˢ Iic (1 : ℝ)) := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [frontier_prod_eq, frontier_univ, empty_prod, union_empty,
      closure_univ, frontier_Iic, mem_prod, mem_univ, mem_singleton_iff, true_and]
    rfl
  have hne : (circleLevelLift '' S).Nonempty := by
    exact ⟨_, mem_image_of_mem _ (b ⟨fun _ ↦ 1, by simp⟩).property⟩
  exact hd'.isFinitePLBallPair_radial_cone hcv hzero hboundary hne
    (isCompact_closedBall _ _) (convex_closedBall _ _)
    ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩


def capSign (positive : Bool) : ℝ := if positive then 1 else -1

noncomputable def capRebase (positive : Bool) : (E × ℝ) →ᴬ[ℝ] (E × ℝ) :=
  (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap.prod
    ((ContinuousAffineMap.const ℝ (E × ℝ) (capSign positive)) -
      capSign positive • (ContinuousLinearMap.snd ℝ E ℝ).toContinuousAffineMap)

omit [FiniteDimensional ℝ E] in
theorem capRebase_injective (positive : Bool) :
    Function.Injective (capRebase (E := E) positive) := by
  intro x y hxy
  have hf := congrArg Prod.fst hxy
  change x.1 = y.1 at hf
  apply Prod.ext hf
  have ht := congrArg Prod.snd hxy
  change capSign positive - capSign positive * x.2 =
    capSign positive - capSign positive * y.2 at ht
  cases positive <;> simp only [capSign, Bool.false_eq_true, if_false, if_true] at ht <;> linarith



def boundaryCircleCap (positive : Bool) (S : Set E) : Set (E × ℝ) :=
  capRebase positive '' boundaryCircleCone S

omit [FiniteDimensional ℝ E] in
theorem mem_boundaryCircleCap_iff (positive : Bool) (S : Set E) (x : E × ℝ) :
    x ∈ boundaryCircleCap positive S ↔
      ∃ y ∈ S, ∃ r ∈ Icc (0 : ℝ) 1, x = (r • y, capSign positive * (1 - r)) := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨y, hy, r, hr, rfl⟩ := (mem_boundaryCircleCone_iff S z).mp hz
    refine ⟨y, hy, r, hr, ?_⟩
    apply Prod.ext
    · rfl
    · change capSign positive - capSign positive * r = capSign positive * (1 - r)
      ring
  · rintro ⟨y, hy, r, hr, rfl⟩
    refine ⟨(r • y, r), (mem_boundaryCircleCone_iff S _).mpr ⟨y, hy, r, hr, rfl⟩, ?_⟩
    apply Prod.ext
    · rfl
    · change capSign positive - capSign positive * r = capSign positive * (1 - r)
      ring

omit [FiniteDimensional ℝ E] in
theorem boundaryCircleCap_plane (positive : Bool) (S : Set E) :
    boundaryCircleCap positive S ∩ ((univ : Set E) ×ˢ {0}) = S ×ˢ {0} := by
  ext x
  constructor
  · rintro ⟨hx, hxplane⟩
    obtain ⟨y, hy, r, hr, rfl⟩ := (mem_boundaryCircleCap_iff positive S x).mp hx
    have ht : capSign positive * (1 - r) = 0 := hxplane.2
    have hr1 : r = 1 := by cases positive <;> simp [capSign] at ht <;> linarith
    simpa only [hr1, one_smul, sub_self, mul_zero, mem_prod, mem_singleton_iff, and_true]
      using hy
  · rintro ⟨hx, hx0⟩
    refine ⟨(mem_boundaryCircleCap_iff positive S x).mpr
      ⟨x.1, hx, 1, ⟨zero_le_one, le_rfl⟩, ?_⟩, mem_univ _, hx0⟩
    exact Prod.ext (one_smul ℝ x.1).symm (by simpa using hx0)

omit [FiniteDimensional ℝ E] in
theorem boundaryCircleCaps_disjoint {S T : Set E} (hST : Disjoint S T) :
    Disjoint (boundaryCircleCap false S) (boundaryCircleCap true T) := by
  apply disjoint_left.mpr
  intro x hx hy
  obtain ⟨y, hyS, r, hr, hx⟩ := (mem_boundaryCircleCap_iff false S x).mp hx
  obtain ⟨z, hzT, t, ht, hy⟩ := (mem_boundaryCircleCap_iff true T x).mp hy
  have hheight := congrArg Prod.snd (hx.symm.trans hy)
  simp only [capSign, Bool.false_eq_true, if_false, if_true, neg_mul, one_mul] at hheight
  have hr1 : r = 1 := by linarith [hr.2, ht.2]
  have ht1 : t = 1 := by linarith [hr.2, ht.2]
  have heq := congrArg Prod.fst (hx.symm.trans hy)
  simp only [hr1, ht1, one_smul] at heq
  exact disjoint_left.mp hST hyS (heq.symm ▸ hzT)

theorem isFinitePLBallPair_boundaryCircleCap (positive : Bool) {S : Set E}
    (b : Q2 ≃ₜ S) (hb : b.IsFinitePL) :
    IsFinitePLBallPair V2 (boundaryCircleCap positive S) (S ×ˢ {0}) := by
  have hd := (isFinitePLBallPair_boundaryCircleCone b hb).affine_image
    (capRebase positive) (capRebase_injective positive).injOn
  have himage : capRebase positive '' (circleLevelLift '' S) = S ×ˢ {0} := by
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨hy, by change capSign positive - capSign positive * 1 = 0; ring⟩
    · rintro ⟨hx, hx0⟩
      refine ⟨circleLevelLift x.1, mem_image_of_mem _ hx, ?_⟩
      apply Prod.ext (show ((capRebase positive) (circleLevelLift x.1)).1 = x.1 from rfl)
      change capSign positive - capSign positive * 1 = x.2
      rw [show x.2 = 0 from hx0]
      ring
  rwa [himage] at hd



theorem exists_boundaryCircleCap_parametrization (positive : Bool) {S : Set E}
    (b : Q2 ≃ₜ S) (hb : b.IsFinitePL) :
    ∃ H : closedBall (0 : V2) 1 ≃ₜ boundaryCircleCap positive S, H.IsFinitePL ∧
      (∀ x : Q2, (H ⟨x, sphere_subset_closedBall x.property⟩ : E × ℝ) = ((b x : E), 0)) ∧
      ∀ x : closedBall (0 : V2) 1, (H x : E × ℝ).2 = 0 ↔ (x : V2) ∈ Q2 := by
  let z : E →ᴬ[ℝ] (E × ℝ) :=
    (ContinuousAffineMap.id ℝ E).prod (ContinuousAffineMap.const ℝ E 0)
  obtain ⟨_, ⟨K, hK, hKs, _⟩, _⟩ := hb.symm
  have hz : FinitePiecewiseAffineOn z S := ⟨K, hK, hKs, K.affineOnFaces_affine z⟩
  obtain ⟨c, hc, hvalues⟩ := hz.exists_homeomorph_image
    (fun x _ y _ heq ↦ congrArg Prod.fst heq)
  have himage : z '' S = S ×ˢ {0} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, rfl⟩
    · rintro ⟨hx, hx0⟩
      exact ⟨x.1, hx, Prod.ext rfl hx0.symm⟩
  let gamma := b.trans (c.trans (Homeomorph.setCongr himage))
  have hgamma : gamma.IsFinitePL := hb.trans (hc.setCongr rfl himage)
  obtain ⟨H, hH, hHb, hboundary⟩ :=
    (isFinitePLBallPair_unit_cube (ι := Fin 2)).exists_extension
      (isFinitePLBallPair_boundaryCircleCap positive b hb) gamma hgamma
  refine ⟨H, hH, ?_, ?_⟩
  · intro x
    have hval := congrArg Subtype.val (hHb x)
    exact hval.trans (hvalues (b x))
  · intro x
    have hplane : (H x : E × ℝ).2 = 0 ↔ (H x : E × ℝ) ∈ S ×ˢ {0} := by
      constructor
      · intro ht
        exact (boundaryCircleCap_plane positive S).subset ⟨(H x).property, mem_univ _, ht⟩
      · exact fun ht ↦ ht.2
    exact hplane.trans (hboundary x).symm

end PoincareConjecture.M76.Dehn.Annuli
