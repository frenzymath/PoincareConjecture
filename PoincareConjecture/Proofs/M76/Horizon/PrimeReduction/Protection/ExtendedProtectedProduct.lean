import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.ProtectedEndDiskCollars
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PolyhedralPLClosedUnion



set_option autoImplicit false
noncomputable section
open Set Metric Geometry

namespace PoincareConjecture.M76.ProtectedProductExtension

local notation "P2" => (ℝ × ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (-1 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set P2)
local notation "Cube" => (Square ×ˢ I : Set P3)
local notation "Half" => (Set.prod Square (Icc (0 : ℝ) 1) : Set P3)
local notation "Extended" => (Set.prod Square (Icc (-2 : ℝ) 2) : Set P3)

def endpointCoordinates (side : Bool) : P3 →ᴬ[ℝ] P3 :=
  (ContinuousLinearMap.fst ℝ P2 ℝ).toContinuousAffineMap.prod
    (((if side then (1 : ℝ) else -1) •
      (ContinuousLinearMap.snd ℝ P2 ℝ).toContinuousAffineMap) -
        ContinuousAffineMap.const ℝ P3 1)

def map {X : Type*} (p : P3 → X) (k : Bool → P3 → X) (z : P3) : X :=
  if z.2 < -1 then k false (endpointCoordinates false z)
  else if 1 < z.2 then k true (endpointCoordinates true z) else p z

theorem map_eq_on_cube {X : Type*} (p : P3 → X) (k : Bool → P3 → X) :
    EqOn (map p k) p Cube := by
  intro z hz
  simp only [map, if_neg (not_lt.mpr hz.2.1), if_neg (not_lt.mpr hz.2.2)]

private theorem exists_box_complex (a b : ℝ) (hab : a < b) :
    ∃ K : SimplicialComplex ℝ P3, K.faces.Finite ∧
      K.space = Square ×ˢ Icc a b := by
  obtain ⟨K, _, hK, hKs, _, _⟩ :=
    (((isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num)).prod
      (isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num))).prod
        (isFinitePLBallPair_Icc hab)).exists_finite_carrier_and_rim_complexes
  exact ⟨K, hK, hKs⟩

theorem polyhedral {X α : Type*} [TopologicalSpace X]
    {e : α → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (p : P3 → X) (k : Bool → P3 → X)
    (hp : PolyhedralPLInCharts e p Cube)
    (hk : ∀ i, PolyhedralPLInCharts e (k i) Half)
    (hzero : ∀ i, ∀ x ∈ Square, k i (x, 0) = p (x, if i then 1 else -1)) :
    PolyhedralPLInCharts e (map p k) Extended := by
  obtain ⟨K, hK, hKs⟩ := exists_box_complex (-1) 1 (by norm_num)
  obtain ⟨L, hL, hLs⟩ := exists_box_complex (-2) (-1) (by norm_num)
  obtain ⟨U, hU, hUs⟩ := exists_box_complex 1 2 (by norm_num)
  have hc : PolyhedralPLInCharts e (map p k) K.space := by
    rw [hKs]
    exact hp.congr (map_eq_on_cube p k).symm
  have hl : PolyhedralPLInCharts e (map p k) L.space := by
    have hm : MapsTo (endpointCoordinates false) L.space Half := by
      intro z hz
      obtain ⟨hz, ht⟩ := hLs.subset hz
      exact ⟨hz, by change 0 ≤ -1 * z.2 - 1 ∧ -1 * z.2 - 1 ≤ 1; constructor <;> linarith [ht.1, ht.2]⟩
    apply ((hk false).comp_finitePiecewiseAffineOn L hL
      ((L.affineOnFaces_affine (endpointCoordinates false)).finitePiecewiseAffineOn hL) hm).congr
    intro z hz
    obtain ⟨hz, ht⟩ := hLs.subset hz
    change k false (endpointCoordinates false z) = map p k z
    by_cases h : z.2 < -1
    · simp only [map, if_pos h]
    · have ht' : z.2 = -1 := le_antisymm ht.2 (le_of_not_gt h)
      have heq : endpointCoordinates false z = (z.1, 0) := by
        apply Prod.ext
        · rfl
        · change -1 * z.2 - 1 = 0
          rw [ht']; ring
      rw [heq, hzero false z.1 hz]
      simp only [Bool.false_eq_true, ↓reduceIte, map, if_neg h]
      rw [if_neg (by linarith : ¬1 < z.2)]
      exact congrArg p (Prod.ext rfl ht'.symm)
  have hu : PolyhedralPLInCharts e (map p k) U.space := by
    have hm : MapsTo (endpointCoordinates true) U.space Half := by
      intro z hz
      obtain ⟨hz, ht⟩ := hUs.subset hz
      exact ⟨hz, by change 0 ≤ 1 * z.2 - 1 ∧ 1 * z.2 - 1 ≤ 1; constructor <;> linarith [ht.1, ht.2]⟩
    apply ((hk true).comp_finitePiecewiseAffineOn U hU
      ((U.affineOnFaces_affine (endpointCoordinates true)).finitePiecewiseAffineOn hU) hm).congr
    intro z hz
    obtain ⟨hz, ht⟩ := hUs.subset hz
    change k true (endpointCoordinates true z) = map p k z
    have hn : ¬ z.2 < -1 := by linarith [ht.1]
    by_cases h : 1 < z.2
    · simp only [map, if_neg hn, if_pos h]
    · have ht' : z.2 = 1 := le_antisymm (le_of_not_gt h) ht.1
      have heq : endpointCoordinates true z = (z.1, 0) := by
        apply Prod.ext
        · rfl
        · change 1 * z.2 - 1 = 0
          rw [ht']; ring
      rw [heq, hzero true z.1 hz]
      simp only [map, if_neg hn, if_neg h, ↓reduceIte]
      exact congrArg p (Prod.ext rfl ht'.symm)
  obtain ⟨KL, hKL, hKLs⟩ := K.exists_finite_triangulation_union L hK hL
  have hcl : PolyhedralPLInCharts e (map p k) KL.space := by
    rw [hKLs]
    exact PolyhedralPLInCharts.union_of_finite he K L hK hL hc hl
  have h := PolyhedralPLInCharts.union_of_finite he KL U hKL hU hcl hu
  have heq : KL.space ∪ U.space = Extended := by
    rw [hKLs, hKs, hLs, hUs]
    ext z
    constructor
    · rintro ((h | h) | h) <;> exact ⟨h.1, by constructor <;> linarith [h.2.1, h.2.2]⟩
    · intro hz
      by_cases hl : z.2 < -1
      · exact Or.inl (Or.inr ⟨hz.1, hz.2.1, hl.le⟩)
      · by_cases hr : 1 < z.2
        · exact Or.inr ⟨hz.1, hr.le, hz.2.2⟩
        · exact Or.inl (Or.inl ⟨hz.1, le_of_not_gt hl, le_of_not_gt hr⟩)
  rwa [heq] at h

theorem map_cases {X : Type*} (p : P3 → X) (k : Bool → P3 → X)
    (z : P3) (hz : z ∈ Extended) :
    (z ∈ Cube ∧ map p k z = p z) ∨
      ∃ i, endpointCoordinates i z ∈ Half ∧
        0 < (endpointCoordinates i z).2 ∧ map p k z = k i (endpointCoordinates i z) := by
  by_cases hl : z.2 < -1
  · right
    refine ⟨false, ⟨hz.1, ?_⟩, ?_, by simp only [map, if_pos hl]⟩
    · change 0 ≤ -1 * z.2 - 1 ∧ -1 * z.2 - 1 ≤ 1
      constructor <;> linarith [hz.2.1]
    · change 0 < -1 * z.2 - 1
      linarith
  · by_cases hr : 1 < z.2
    · right
      refine ⟨true, ⟨hz.1, ?_⟩, ?_, by simp only [map, if_neg hl, if_pos hr]⟩
      · change 0 ≤ 1 * z.2 - 1 ∧ 1 * z.2 - 1 ≤ 1
        constructor <;> linarith [hz.2.2]
      · change 0 < 1 * z.2 - 1
        linarith
    · exact Or.inl ⟨⟨hz.1, le_of_not_gt hl, le_of_not_gt hr⟩,
        by simp only [map, if_neg hl, if_neg hr]⟩

theorem endpointCoordinates_injective (i : Bool) : Function.Injective (endpointCoordinates i) := by
  intro z w h
  have hfst := congrArg Prod.fst h
  have hsnd := congrArg Prod.snd h
  change z.1 = w.1 at hfst
  apply Prod.ext hfst
  cases i
  · change -1 * z.2 - 1 = -1 * w.2 - 1 at hsnd
    linarith
  · change 1 * z.2 - 1 = 1 * w.2 - 1 at hsnd
    linarith

theorem injective {X : Type*} {D : Set X} (p : P3 → X) (k : Bool → P3 → X)
    (hp : InjOn p Cube) (hpD : MapsTo p Cube D)
    (hk : ∀ i, InjOn (k i) Half)
    (hout : ∀ i, ∀ z ∈ Half, 0 < z.2 → k i z ∉ D)
    (hdis : Disjoint (k false '' Half) (k true '' Half)) :
    InjOn (map p k) Extended := by
  intro z hz w hw heq
  rcases map_cases p k z hz with ⟨hzC, hzv⟩ | ⟨i, hzi, hzt, hzv⟩
  · rcases map_cases p k w hw with ⟨hwC, hwv⟩ | ⟨i, hwi, hwt, hwv⟩
    · exact hp hzC hwC (hzv.symm.trans (heq.trans hwv))
    · exact False.elim (hout i _ hwi hwt (by rw [← hwv, ← heq, hzv]; exact hpD hzC))
  · rcases map_cases p k w hw with ⟨hwC, hwv⟩ | ⟨j, hwj, hwt, hwv⟩
    · exact False.elim (hout i _ hzi hzt (by rw [← hzv, heq, hwv]; exact hpD hwC))
    · have he : k i (endpointCoordinates i z) = k j (endpointCoordinates j w) :=
        hzv.symm.trans (heq.trans hwv)
      by_cases hij : i = j
      · subst j
        exact endpointCoordinates_injective i (hk i hzi hwj he)
      · have hzi' : k i (endpointCoordinates i z) ∈ k i '' Half :=
          ⟨_, hzi, rfl⟩
        have hwj' : k i (endpointCoordinates i z) ∈ k j '' Half :=
          ⟨_, hwj, he.symm⟩
        cases i <;> cases j
        · exact False.elim (hij rfl)
        · exact False.elim (Set.disjoint_left.mp hdis hzi' hwj')
        · exact False.elim (Set.disjoint_left.mp hdis hwj' hzi')
        · exact False.elim (hij rfl)

theorem inside {X : Type*} {R : Set X} (p : P3 → X) (k : Bool → P3 → X)
    (hp : MapsTo p Cube R) (hk : ∀ i, MapsTo (k i) Half R) :
    MapsTo (map p k) Extended R := by
  intro z hz
  rcases map_cases p k z hz with ⟨hzC, hval⟩ | ⟨i, hzi, _, hval⟩
  · rw [hval]
    exact hp hzC
  · rw [hval]
    exact hk i hzi

theorem proper {X : Type*} [TopologicalSpace X] {R : Set X}
    (p : P3 → X) (k : Bool → P3 → X)
    (hp : ∀ z ∈ Cube, p z ∈ frontier R ↔ |z.1.1| = 1 ∨ |z.1.2| = 1)
    (hk : ∀ i, ∀ z ∈ Half, k i z ∈ frontier R ↔ |z.1.1| = 1 ∨ |z.1.2| = 1) :
    ∀ z ∈ Extended, map p k z ∈ frontier R ↔ |z.1.1| = 1 ∨ |z.1.2| = 1 := by
  intro z hz
  rcases map_cases p k z hz with ⟨hzC, hval⟩ | ⟨i, hzi, _, hval⟩
  · rw [hval]
    exact hp z hzC
  · rw [hval]
    exact hk i _ hzi

private def pairVector : P2 ≃L[ℝ] (Fin 2 → ℝ) :=
  (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm

private theorem pairVector_mem_disk {x : P2} (hx : x ∈ Square) :
    pairVector x ∈ closedBall (0 : Fin 2 → ℝ) 1 := by
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  fin_cases i
  · exact abs_le.mpr hx.1
  · exact abs_le.mpr hx.2

private theorem pairVector_mem_rim {x : P2} (hx : x ∈ Square) :
    pairVector x ∈ sphere (0 : Fin 2 → ℝ) 1 ↔ |x.1| = 1 ∨ |x.2| = 1 := by
  have hn : ‖pairVector x‖ ≤ 1 := mem_closedBall_zero_iff.mp (pairVector_mem_disk hx)
  rw [mem_sphere_zero_iff_norm]
  constructor
  · intro h
    by_contra! he
    have hlt : ‖pairVector x‖ < 1 := (pi_norm_lt_iff zero_lt_one).mpr (by
      intro i
      fin_cases i
      · exact lt_of_le_of_ne (abs_le.mpr hx.1) he.1
      · exact lt_of_le_of_ne (abs_le.mpr hx.2) he.2)
    linarith
  · rintro (h | h)
    · exact le_antisymm hn (by
        have hh := norm_le_pi_norm (pairVector x) 0
        change |x.1| ≤ ‖pairVector x‖ at hh
        simpa only [h] using hh)
    · exact le_antisymm hn (by
        have hh := norm_le_pi_norm (pairVector x) 1
        change |x.2| ≤ ‖pairVector x‖ at hh
        simpa only [h] using hh)

theorem exists_extension {X α : Type*} [TopologicalSpace X] [T2Space X]
    {e : α → OpenPartialHomeomorph X V3} {R D : Set X}
    (hR : IsCompact R) (he : PLDomain e R) (hDR : D ⊆ R)
    (p : P3 → X) (hp : PolyhedralPLInCharts e p Cube) (hpi : InjOn p Cube)
    (hpimage : p '' Cube = D)
    (hproper : ∀ z ∈ Cube, p z ∈ frontier R ↔ |z.1.1| = 1 ∨ |z.1.2| = 1) :
    ∃ q : P3 → X, PolyhedralPLInCharts e q Extended ∧
      InjOn q Extended ∧ EqOn q p Cube ∧ MapsTo q Extended R ∧
      ∀ z ∈ Extended, q z ∈ frontier R ↔ |z.1.1| = 1 ∨ |z.1.2| = 1 := by
  obtain ⟨P, δ, positive, hdis, hδ⟩ :=
    exists_disjoint_outward_products_at_protected_endpoints hR he hDR p hp hpi hpimage hproper
  let c : Bool → ℝ := fun i => if positive i then -(δ i) / 2 else δ i / 2
  have hc0 (i : Bool) : c i ≠ 0 := by
    have := (hδ i).1
    dsimp [c]
    split_ifs <;> linarith
  have hcb (i : Bool) : |c i| ≤ 1 := by
    have := (hδ i).1
    have := (hδ i).2.1
    dsimp [c]
    split_ifs <;> apply abs_le.mpr <;> constructor <;> linarith
  let a (i : Bool) : P3 →ᴬ[ℝ] ((Fin 2 → ℝ) × ℝ) :=
    (pairVector.toContinuousLinearMap.comp (ContinuousLinearMap.fst ℝ P2 ℝ)).toContinuousAffineMap.prod
      (c i • (ContinuousLinearMap.snd ℝ P2 ℝ).toContinuousAffineMap)
  have ha (i : Bool) : MapsTo (a i) Half (closedBall (0 : Fin 2 → ℝ) 1 ×ˢ I) := by
    intro z hz
    refine ⟨pairVector_mem_disk hz.1, ?_⟩
    change -1 ≤ c i * z.2 ∧ c i * z.2 ≤ 1
    apply abs_le.mp
    rw [abs_mul, abs_of_nonneg hz.2.1]
    exact (mul_le_mul_of_nonneg_left hz.2.2 (abs_nonneg _)).trans (by simpa using hcb i)
  have hai (i : Bool) : Function.Injective (a i) := by
    intro z w h
    have hf := congrArg Prod.fst h
    have ht := congrArg Prod.snd h
    change pairVector z.1 = pairVector w.1 at hf
    change c i * z.2 = c i * w.2 at ht
    exact Prod.ext (pairVector.injective hf) (mul_left_cancel₀ (hc0 i) ht)
  let k : Bool → P3 → X := fun i => (P i).map ∘ a i
  have hkPL (i : Bool) : PolyhedralPLInCharts e (k i) Half := by
    obtain ⟨K, hK, hKs⟩ := exists_box_complex 0 1 (by norm_num)
    change K.space = Half at hKs
    rw [← hKs]
    exact (P i).polyhedral.comp_finitePiecewiseAffineOn K hK
      ((K.affineOnFaces_affine (a i)).finitePiecewiseAffineOn hK)
      (fun z hz => ha i (hKs.subset hz))
  have hki (i : Bool) : InjOn (k i) Half := (P i).injective.comp (hai i).injOn (ha i)
  have hkR (i : Bool) : MapsTo (k i) Half R := (P i).inside.comp (ha i)
  have hk0 (i : Bool) (x : P2) (hx : x ∈ Square) :
      k i (x, 0) = p (x, if i then 1 else -1) := by
    have hav : a i (x, 0) = (pairVector x, 0) := by
      apply Prod.ext
      · rfl
      · exact mul_zero _
    change (P i).map (a i (x, 0)) = _
    rw [hav, (P i).central _ (pairVector_mem_disk hx)]
    rfl
  have hkout (i : Bool) (z : P3) (hz : z ∈ Half) (ht : 0 < z.2) : k i z ∉ D := by
    apply (hδ i).2.2 ⟨pairVector z.1, (ha i hz).1⟩ ⟨c i * z.2, (ha i hz).2⟩
    have hδp := (hδ i).1
    have hδb := (hδ i).2.1
    dsimp only
    cases hpos : positive i
    · simp only [Bool.false_eq_true, ↓reduceIte]
      change 0 < c i * z.2 ∧ c i * z.2 ≤ δ i
      dsimp [c]
      rw [hpos]
      simp only [Bool.false_eq_true, ↓reduceIte]
      constructor
      · exact mul_pos (by linarith) ht
      · nlinarith [hz.2.2]
    · simp only [↓reduceIte]
      change -(δ i) ≤ c i * z.2 ∧ c i * z.2 < 0
      dsimp [c]
      rw [hpos]
      simp only [↓reduceIte]
      constructor
      · nlinarith [hz.2.2]
      · exact mul_neg_of_neg_of_pos (by linarith) ht
  have hkdis : Disjoint (k false '' Half) (k true '' Half) :=
    hdis.mono (by rintro _ ⟨z, hz, heq⟩; exact ⟨a false z, ha false hz, heq⟩)
      (by rintro _ ⟨z, hz, heq⟩; exact ⟨a true z, ha true hz, heq⟩)
  have hkproper (i : Bool) (z : P3) (hz : z ∈ Half) :
      k i z ∈ frontier R ↔ |z.1.1| = 1 ∨ |z.1.2| = 1 :=
    ((P i).proper (a i z) (ha i hz)).trans (pairVector_mem_rim hz.1)
  refine ⟨map p k, polyhedral he.compatible p k hp hkPL hk0,
    injective p k hpi (fun z hz => hpimage.subset ⟨z, hz, rfl⟩) hki hkout hkdis,
    map_eq_on_cube p k,
    inside p k (fun z hz => hDR (hpimage.subset ⟨z, hz, rfl⟩)) hkR,
    proper p k hproper hkproper⟩

end PoincareConjecture.M76.ProtectedProductExtension
