import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.SphereCutPLDomain
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.FiniteSphereBicollars
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.FiniteCutPLDomain

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "J" => Icc (-1 : ℝ) 1

theorem exists_original_finite_pl_sphere_cut
    {X ι κ : Type*} [MetricSpace X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {R U : Set X}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hR : IsCompact R) (he : PLDomain e R)
    (hSR : ∀ i, S i ⊆ interior R) (hU : IsOpen U) (hSU : ∀ i, S i ⊆ U) :
    ∃ (t : κ → Finset R)
      (N : ∀ i, SimplicialComplex ℝ (t i → ℝ × (Fin 3 → ℝ)))
      (HB : ∀ i, (N i).space ≃ₜ S i)
      (c : ∀ i, (t i → ℝ × (Fin 3 → ℝ)) × ℝ → X)
      (ε : κ → ℝ) (Q : Set X) (B : κ × Bool → Set X)
      (H : ∀ b, S b.1 ≃ₜ B b)
      (_sB : ∀ b, ChartwisePLSphere e (B b)),
      let O : κ → Set X := fun i => c i '' ((N i).space ×ˢ Ioo (-ε i) (ε i))
      let C : κ → Set X := fun i => c i '' ((N i).space ×ˢ Icc (-ε i) (ε i))
      (∀ i, (N i).faces.Finite ∧
        PolyhedralPLInCharts e (c i) ((N i).space ×ˢ Icc (-1 : ℝ) 1) ∧
        Topology.IsEmbedding (fun z : ((N i).space ×ˢ Icc (-1 : ℝ) 1 :
          Set ((t i → ℝ × (Fin 3 → ℝ)) × ℝ)) => c i z) ∧
        (∀ x : (N i).space, c i ((x : t i → ℝ × (Fin 3 → ℝ)), 0) = HB i x) ∧
        0 < ε i ∧ ε i ≤ 1 / 4 ∧ IsOpen (O i) ∧
        IsCompact (C i) ∧ closure (O i) = C i ∧ C i ⊆ U ∩ interior R) ∧
      Pairwise (fun i j => Disjoint (C i) (C j)) ∧
      (∀ b, B b = c b.1 '' ((N b.1).space ×ˢ
        ({if b.2 then ε b.1 else -ε b.1} : Set ℝ))) ∧
      (∀ b (x : S b.1), (H b x : X) =
        c b.1 (((HB b.1).symm x : t b.1 → ℝ × (Fin 3 → ℝ)),
          if b.2 then ε b.1 else -ε b.1)) ∧
      Pairwise (fun b d => Disjoint (B b) (B d)) ∧
      (⋃ b, B b) ⊆ U ∩ interior R ∧
      Q = R \ ⋃ i, O i ∧ IsCompact Q ∧ PLDomain e Q ∧
      interior Q = interior R \ ⋃ i, C i ∧
      frontier Q = frontier R ∪ ⋃ b, B b ∧
      (∀ i, C i ∩ Q = B (i, false) ∪ B (i, true)) ∧
      (⋃ i, C i) ∩ Q = ⋃ b, B b ∧
      (⋃ i, C i) ∪ Q = R ∧
      Disjoint (frontier R) (⋃ b, B b) ∧ frontier R ⊆ Q ∧
      Q \ U = R \ U ∧ Disjoint (⋃ i, S i) Q := by
  classical
  obtain ⟨t, F, N, HB, c, δ, hFmodel, hmodel, hlargeDisjoint⟩ :=
    exists_original_finite_sphere_bicollars_with_model S sS hdis hR he hSR hU hSU
  let ε : κ → ℝ := fun i => δ i / 2
  let O : κ → Set X := fun i => c i '' ((N i).space ×ˢ Ioo (-ε i) (ε i))
  let C : κ → Set X := fun i => c i '' ((N i).space ×ˢ Icc (-ε i) (ε i))
  let level : κ × Bool → ℝ := fun b => if b.2 then ε b.1 else -ε b.1
  let B : κ × Bool → Set X := fun b => c b.1 '' ((N b.1).space ×ˢ ({level b} : Set ℝ))
  have hwidth (i : κ) : 0 < ε i ∧ ε i ≤ 1 / 4 ∧ ε i < δ i ∧ δ i ≤ 1 := by
    obtain ⟨_, _, _, _, _, _, hd, hds, _⟩ := hmodel i
    dsimp [ε]
    constructor
    · linarith
    constructor
    · linarith
    constructor <;> linarith
  have hεone (i : κ) : ε i ≤ 1 := by linarith [(hwidth i).2.1]
  have hsmall (i : κ) :
      (N i).space ×ˢ Icc (-ε i) (ε i) ⊆ (N i).space ×ˢ Icc (-δ i) (δ i) := by
    rintro ⟨x, r⟩ ⟨hx, hr⟩
    exact ⟨hx, by constructor <;> linarith [hr.1, hr.2, (hwidth i).2.2.1]⟩
  have hclosedDisjoint : Pairwise (fun i j => Disjoint (C i) (C j)) := by
    intro i j hij
    exact (hlargeDisjoint hij).mono (image_mono (hsmall i)) (image_mono (hsmall j))
  have hlevel (b : κ × Bool) : level b ∈ J := by
    rcases b with ⟨i, b⟩
    cases b <;> simp only [level, Bool.false_eq_true, ↓reduceIte] <;>
      constructor <;> linarith [(hwidth i).1, hεone i]
  have hlevelSmall (b : κ × Bool) : level b ∈ Icc (-ε b.1) (ε b.1) := by
    rcases b with ⟨i, b⟩
    cases b <;> simp only [level, Bool.false_eq_true, ↓reduceIte] <;>
      constructor <;> linarith [(hwidth i).1]
  have hBsub (b : κ × Bool) : B b ⊆ C b.1 := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, ⟨hz.1, (show z.2 = level b from hz.2) ▸ hlevelSmall b⟩, rfl⟩
  have hstrips : ∀ i, IsOpen (O i) ∧ IsCompact (C i) ∧ closure (O i) = C i ∧
      frontier (O i) = B (i, false) ∪ B (i, true) := by
    intro i
    obtain ⟨hN, hPL, hc, _, _, _, _, _, _, ho⟩ := hmodel i
    have hA := (N i).isCompact_space_of_finite hN
    have hopen := ho (ε i) (hwidth i).1 (hwidth i).2.2.1.le
    have hsub : (N i).space ×ˢ Icc (-ε i) (ε i) ⊆ (N i).space ×ˢ J := by
      rintro ⟨x, r⟩ ⟨hx, hr⟩
      exact ⟨hx, by constructor <;> linarith [hr.1, hr.2, hεone i]⟩
    exact ⟨hopen, (hA.prod isCompact_Icc).image_of_continuousOn (hPL.continuousOn.mono hsub),
      hPL.continuousOn.closure_image_collar_strip hA (hwidth i).1 (hεone i),
      hc.frontier_image_collar_strip hA (hwidth i).1 (hεone i) hopen⟩
  have hclosedInside (i : κ) : C i ⊆ U ∩ interior R := by
    obtain ⟨_, _, _, _, _, _, _, _, hi, _⟩ := hmodel i
    rintro _ ⟨z, hz, rfl⟩
    exact hi (hsmall i hz)
  have hclosureInside (i : κ) : closure (O i) ⊆ interior R := by
    rw [(hstrips i).2.2.1]
    exact fun _ hx => (hclosedInside i hx).2
  have hclosureDisjoint : Pairwise (fun i j => Disjoint (closure (O i)) (closure (O j))) := by
    intro i j hij
    simpa only [(hstrips i).2.2.1, (hstrips j).2.2.1] using hclosedDisjoint hij
  have hspheres (b : κ × Bool) : Nonempty (ChartwisePLSphere e (B b)) := by
    obtain ⟨_, hF, hFi, hNs⟩ := hFmodel b.1
    obtain ⟨_, hPL, hc, _⟩ := hmodel b.1
    obtain ⟨q, _⟩ := (sS b.1).exists_bicollar_level_sphere (F b.1) hF
      (hFi.mono ((hSR b.1).trans interior_subset)) hNs (c b.1) hPL hc (hlevel b)
    exact ⟨q⟩
  let sB : ∀ b, ChartwisePLSphere e (B b) := fun b => Classical.choice (hspheres b)
  have hcut (i : κ) : PLDomain e (R \ O i) := by
    obtain ⟨_, hF, hFi, hNs⟩ := hFmodel i
    obtain ⟨hN, hPL, hc, _, _, _, _, _, hi, _⟩ := hmodel i
    exact (sS i).plDomain_bicollar_cut hR he (F i) hF
      (hFi.mono ((hSR i).trans interior_subset)) hNs ((N i).isCompact_space_of_finite hN)
      (c i) hPL hc (hwidth i).1 (hwidth i).2.2.1 (hwidth i).2.2.2
      (fun _ hz => (hi hz).2) (hstrips i).1
  have hmarked : ∀ b : κ × Bool, ∃ Hb : S b.1 ≃ₜ B b,
      ∀ x, (Hb x : X) = c b.1 (((HB b.1).symm x : t b.1 → ℝ × V3), level b) := by
    intro b
    obtain ⟨hN, _, hc, _⟩ := hmodel b.1
    obtain ⟨H, hH, _⟩ := exists_collar_level_homeomorph
      ((N b.1).isCompact_space_of_finite hN) (c b.1) hc (hlevel b)
    exact ⟨(HB b.1).symm.trans H, fun x => hH ((HB b.1).symm x)⟩
  choose H hH using hmarked
  have hBdisjoint : Pairwise (fun b d => Disjoint (B b) (B d)) := by
    intro b d hbd
    by_cases hi : b.1 = d.1
    · rcases b with ⟨i, b⟩
      rcases d with ⟨j, d⟩
      change i = j at hi
      subst j
      obtain ⟨_, _, hc, _⟩ := hmodel i
      have hl : level (i, b) ≠ level (i, d) := by
        cases b <;> cases d
        · exact False.elim (hbd rfl)
        · dsimp [level]
          linarith [(hwidth i).1]
        · dsimp [level]
          linarith [(hwidth i).1]
        · exact False.elim (hbd rfl)
      exact disjoint_collar_level_images (c i) hc (hlevel (i, b)) (hlevel (i, d)) hl
    · exact (hclosedDisjoint hi).mono (hBsub b) (hBsub d)
  have hfrontUnion : (⋃ i, frontier (O i)) = ⋃ b, B b := by
    simp only [(hstrips _).2.2.2]
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      rcases hi with hi | hi
      · exact mem_iUnion.mpr ⟨(i, false), hi⟩
      · exact mem_iUnion.mpr ⟨(i, true), hi⟩
    · intro hx
      obtain ⟨⟨i, b⟩, hi⟩ := mem_iUnion.mp hx
      apply mem_iUnion.mpr
      refine ⟨i, ?_⟩
      cases b
      · exact Or.inl hi
      · exact Or.inr hi
  have hclosureUnion : (⋃ i, closure (O i)) = ⋃ i, C i := by
    simp only [(hstrips _).2.2.1]
  obtain ⟨hQ, hQi, hQf, hoverlap, hallOverlap, hcover, _, holdDisjoint, hold⟩ :=
    finite_collar_cut_geometry hR (fun i => (hstrips i).1) hclosureInside hclosureDisjoint
  let Q := R \ ⋃ i, O i
  have hQPL : PLDomain e Q := he.sdiff_iUnion_of_disjoint_collar_closures hR
    (fun i => (hstrips i).1) hclosureInside hclosureDisjoint hcut
  have hSQ : Disjoint (⋃ i, S i) Q := by
    apply disjoint_left.mpr
    intro x hx hxQ
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    obtain ⟨_, _, _, _, hc0, _⟩ := hmodel i
    let y := (HB i).symm ⟨x, hxi⟩
    apply hxQ.2
    apply mem_iUnion.mpr
    refine ⟨i, ((y : t i → ℝ × V3), 0), ⟨y.property, ?_, (hwidth i).1⟩, ?_⟩
    · linarith [(hwidth i).1]
    · exact (hc0 y).trans (congrArg Subtype.val ((HB i).apply_symm_apply ⟨x, hxi⟩))
  have houtside : Q \ U = R \ U := by
    ext x
    constructor
    · exact fun hx => ⟨hx.1.1, hx.2⟩
    · rintro ⟨hxR, hxU⟩
      refine ⟨⟨hxR, ?_⟩, hxU⟩
      intro hxO
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hxO
      have hxC : x ∈ C i := (hstrips i).2.2.1.subset (subset_closure hxi)
      exact hxU (hclosedInside i hxC).1
  refine ⟨t, N, HB, c, ε, Q, B, H, sB, ?_, hclosedDisjoint,
    (fun _ => rfl), hH, hBdisjoint, ?_, rfl, hQ, hQPL, ?_, ?_, ?_, ?_, ?_,
    ?_, hold, houtside, hSQ⟩
  · intro i
    obtain ⟨hN, hPL, hc, _, hc0, _⟩ := hmodel i
    exact ⟨hN, hPL, hc, hc0, (hwidth i).1, (hwidth i).2.1,
      (hstrips i).1, (hstrips i).2.1, (hstrips i).2.2.1, hclosedInside i⟩
  · intro x hx
    obtain ⟨b, hb⟩ := mem_iUnion.mp hx
    exact hclosedInside b.1 (hBsub b hb)
  · simpa only [hclosureUnion] using hQi
  · simpa only [hfrontUnion] using hQf
  · intro i
    simpa only [(hstrips i).2.2.1, (hstrips i).2.2.2] using hoverlap i
  · simpa only [hclosureUnion, hfrontUnion] using hallOverlap
  · simpa only [hclosureUnion] using hcover
  · simpa only [hfrontUnion] using holdDisjoint

end PoincareConjecture.M76
