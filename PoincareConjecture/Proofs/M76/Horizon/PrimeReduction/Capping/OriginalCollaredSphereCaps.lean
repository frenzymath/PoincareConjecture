import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.FiniteSphereCutBoundaryCollars
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.OriginalDomainCaps
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.Collars.OriginalCollarModel

set_option autoImplicit false
set_option maxHeartbeats 1800000

open Set Geometry Geometry.SeparatedSphereCaps

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "J" => Icc (-1 : ℝ) 1
local notation "I" => Icc (0 : ℝ) 1

theorem exists_original_collared_sphere_caps
    {X ι κ : Type*} [MetricSpace X] [Fintype κ] [DecidableEq κ]
    {e : ι → OpenPartialHomeomorph X V3} {R U : Set X}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hR : IsCompact R) (he : PLDomain e R)
    (hSR : ∀ i, S i ⊆ interior R) (hU : IsOpen U) (hSU : ∀ i, S i ⊆ U) :
    ∃ (t₀ : κ → Finset R)
      (N : ∀ i, SimplicialComplex ℝ (t₀ i → ℝ × V3))
      (HB : ∀ i, (N i).space ≃ₜ S i)
      (c : ∀ i, (t₀ i → ℝ × V3) × ℝ → X) (δ : κ → ℝ)
      (d : ∀ i, Bool → (t₀ i → ℝ × V3) × ℝ → X),
      let Q := R \ ⋃ i, c i '' ((N i).space ×ˢ Ioo (-(δ i / 2)) (δ i / 2))
      let B : κ × Bool → Set X := fun b => c b.1 '' ((N b.1).space ×ˢ
        ({if b.2 then δ b.1 / 2 else -(δ b.1 / 2)} : Set ℝ))
      ∃ (PB : ∀ b, (N b.1).space ≃ₜ B b)
        (_sB : ∀ b, ChartwisePLSphere e (B b))
        (t : Finset Q) (F : X → (t → ℝ × V3))
        (K L : SimplicialComplex ℝ (t → ℝ × V3)) (H : Q ≃ₜ K.space)
        (C : SimplicialComplex ℝ ((t → ℝ × V3) × ((κ × Bool) → ℝ))),
        (∀ i, (N i).faces.Finite ∧
          PolyhedralPLInCharts e (c i) ((N i).space ×ˢ J) ∧
          Topology.IsEmbedding (fun z : ((N i).space ×ˢ J :
            Set ((t₀ i → ℝ × V3) × ℝ)) => c i z) ∧
          (∀ x : (N i).space, c i ((x : t₀ i → ℝ × V3), 0) = HB i x) ∧
          0 < δ i ∧ δ i ≤ 1 / 2 ∧
          MapsTo (c i) ((N i).space ×ˢ Icc (-δ i) (δ i)) (U ∩ interior R)) ∧
        (∀ i, IsOpen (c i '' ((N i).space ×ˢ Ioo (-(δ i / 2)) (δ i / 2)))) ∧
        Pairwise (fun i j => Disjoint
          (c i '' ((N i).space ×ˢ Icc (-(δ i / 2)) (δ i / 2)))
          (c j '' ((N j).space ×ˢ Icc (-(δ j / 2)) (δ j / 2)))) ∧
        (∀ i b x r, d i b (x, r) = c i (x,
          if b then δ i / 2 + (δ i - δ i / 2) * r
          else -(δ i / 2 + (δ i - δ i / 2) * r))) ∧
        (∀ b (x : (N b.1).space), (PB b x : X) =
          c b.1 ((x : t₀ b.1 → ℝ × V3),
            if b.2 then δ b.1 / 2 else -(δ b.1 / 2))) ∧
        IsCompact Q ∧ PLDomain e Q ∧
        frontier Q = frontier R ∪ ⋃ b, B b ∧
        Pairwise (fun b a => Disjoint (B b) (B a)) ∧
        (⋃ b, B b) ⊆ U ∩ interior R ∧
        (Continuous F ∧
          (∀ j, LocallyPiecewiseAffineOn (F ∘ (e j).symm) (e j).target) ∧
          InjOn F Q ∧ K.faces.Finite ∧ L ≤ K ∧ L.faces.Finite ∧
          K.space = F '' Q ∧ L.space = F '' frontier Q ∧
          (∀ x : Q, (H x : t → ℝ × V3) = F x) ∧
          (∀ z : K.space, F (H.symm z) = (z : t → ℝ × V3)) ∧
          (∀ x : Q, (H x : t → ℝ × V3) ∈ L.space ↔ (x : X) ∈ frontier Q) ∧
          (∀ x ∈ Q, ∃ (j : ι) (V : Set X) (a : (t → ℝ × V3) →ᴬ[ℝ] V3),
            IsOpen V ∧ x ∈ V ∧ V ⊆ (e j).source ∧ EqOn (a ∘ F) (e j) V) ∧
          (∀ i, F '' B i ⊆ L.space) ∧
          (∀ i, ∃ Q : B i ≃ₜ (lift '' (F '' B i) : Set ((t → ℝ × V3) × ((κ × Bool) → ℝ))),
            ∀ x : B i, (Q x : (t → ℝ × V3) × ((κ × Bool) → ℝ)) = lift (F x)) ∧
          (∀ i, IsFinitePLBallPair V3 (cap i (F '' B i)) (lift '' (F '' B i))) ∧
          (∀ i, cap i (F '' B i) ∩ lift '' K.space = lift '' (F '' B i)) ∧
          Pairwise (fun i j => Disjoint (cap i (F '' B i)) (cap j (F '' B j))) ∧
          C.faces.Finite ∧ C.space = lift '' K.space ∪ ⋃ i, cap i (F '' B i)) ∧
        IsCompact (lift '' K.space : Set ((t → ℝ × V3) × ((κ × Bool) → ℝ))) ∧
        ∀ b, ∃ (g : ((t → ℝ × V3) × ((κ × Bool) → ℝ)) × ℝ →
              (t → ℝ × V3) × ((κ × Bool) → ℝ))
          (G : ((lift '' (F '' B b)) ×ˢ I :
              Set (((t → ℝ × V3) × ((κ × Bool) → ℝ)) × ℝ)) ≃ₜ
            g '' ((lift '' (F '' B b)) ×ˢ I)),
          G.IsFinitePL ∧
          (∀ z, (G z : (t → ℝ × V3) × ((κ × Bool) → ℝ)) = g z) ∧
          MapsTo g ((lift '' (F '' B b)) ×ˢ I) (lift '' K.space) ∧
          (∀ x ∈ lift '' (F '' B b), g (x, 0) = x) ∧
          (∀ z ∈ (lift '' (F '' B b)) ×ˢ I, g z ∈ lift '' (F '' B b) ↔ z.2 = 0) ∧
          (∀ (x : (N b.1).space) (r : I),
            g (lift (F (PB b x)), (r : ℝ)) =
              lift (F (d b.1 b.2 ((x : t₀ b.1 → ℝ × V3), (r : ℝ))))) ∧
          ∀ η : ℝ, 0 < η → η ≤ 1 / 2 →
            IsOpen ((Subtype.val :
                (lift '' K.space : Set ((t → ℝ × V3) × ((κ × Bool) → ℝ))) →
                  (t → ℝ × V3) × ((κ × Bool) → ℝ)) ⁻¹'
              (g '' ((lift '' (F '' B b)) ×ˢ Ico 0 η))) := by
  classical
  obtain ⟨t₀, F₀, N, HB, c, δ, hFmodel, hmodel, hlargeDisjoint,
      d, hd, hQcompact, hQPL, hddata⟩ :=
    exists_original_finite_cut_boundary_collars S sS hdis hR he hSR hU hSU
  let ε : κ → ℝ := fun i => δ i / 2
  let O : κ → Set X := fun i => c i '' ((N i).space ×ˢ Ioo (-ε i) (ε i))
  let Cs : κ → Set X := fun i => c i '' ((N i).space ×ˢ Icc (-ε i) (ε i))
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
  have hclosedDisjoint : Pairwise (fun i j => Disjoint (Cs i) (Cs j)) := by
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
  have hBsub (b : κ × Bool) : B b ⊆ Cs b.1 := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, ⟨hz.1, (show z.2 = level b from hz.2) ▸ hlevelSmall b⟩, rfl⟩
  have hstrips : ∀ i, IsOpen (O i) ∧ IsCompact (Cs i) ∧ closure (O i) = Cs i ∧
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
  have hclosedInside (i : κ) : Cs i ⊆ U ∩ interior R := by
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
    obtain ⟨q, _⟩ := (sS b.1).exists_bicollar_level_sphere (F₀ b.1) hF
      (hFi.mono ((hSR b.1).trans interior_subset)) hNs (c b.1) hPL hc (hlevel b)
    exact ⟨q⟩
  let sB : ∀ b, ChartwisePLSphere e (B b) := fun b => Classical.choice (hspheres b)
  have hmarked : ∀ b : κ × Bool, ∃ Pb : (N b.1).space ≃ₜ B b,
      ∀ x, (Pb x : X) = c b.1 ((x : t₀ b.1 → ℝ × V3), level b) := by
    intro b
    obtain ⟨hN, _, hc, _⟩ := hmodel b.1
    obtain ⟨P, hP, _⟩ := exists_collar_level_homeomorph
      ((N b.1).isCompact_space_of_finite hN) (c b.1) hc (hlevel b)
    exact ⟨P, hP⟩
  choose PB hPB using hmarked
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
  let Q := R \ ⋃ i, O i
  have hQfront : frontier Q = frontier R ∪ ⋃ b, B b := by
    have h := (finite_collar_cut_geometry hR (fun i => (hstrips i).1)
      hclosureInside hclosureDisjoint).2.2.1
    simpa only [hfrontUnion] using h
  have hBfront (b : κ × Bool) : B b ⊆ frontier Q := by
    intro x hx
    rw [hQfront]
    exact Or.inr (mem_iUnion.mpr ⟨b, hx⟩)
  obtain ⟨t, F, K, L, H, C, hcaps⟩ :=
    exists_original_domain_capped_complex hQcompact hQPL B sB hBfront hBdisjoint
  have hcapsRetained := hcaps
  obtain ⟨hFc, hF, hFi, hK, hLK, hL, hKs, hLs, hHF, hFH,
    hbound, hproj, hBL, hmark, hball, hinter, hcapDis, hC, hCs⟩ := hcaps
  refine ⟨t₀, N, HB, c, δ, d, PB, sB, t, F, K, L, H, C, ?_,
    (fun i => (hstrips i).1),hclosedDisjoint,hd,hPB,
    hQcompact, hQPL, hQfront, hBdisjoint, ?_, hcapsRetained, ?_, ?_⟩
  · intro i
    obtain ⟨hN, hPL, hc, _, hc0, _, hδ, hδsmall, hconf, _⟩ := hmodel i
    exact ⟨hN, hPL, hc, hc0, hδ, hδsmall, hconf⟩
  · intro x hx
    obtain ⟨b, hb⟩ := mem_iUnion.mp hx
    exact hclosedInside b.1 (hBsub b hb)
  · exact (K.isCompact_space_of_finite hK).image
      (show Continuous (lift : (t → ℝ × V3) →
        (t → ℝ × V3) × ((κ × Bool) → ℝ)) from continuous_id.prodMk continuous_const)
  · intro b
    obtain ⟨hPL, hemb, hmap, _, hbase, _, hopen⟩ := hddata b.1 b.2
    have hinj : InjOn (d b.1 b.2) ((N b.1).space ×ˢ I) := by
      intro x hx y hy hxy
      exact congrArg Subtype.val (hemb.injective
        (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
    exact exists_lifted_original_boundary_collar
      (N b.1) (hmodel b.1).1 (d b.1 b.2) hPL hinj hmap (PB b)
      (fun x => (hbase (x : t₀ b.1 → ℝ × V3)).trans (hPB b x).symm)
      F hF hFi K hK H hHF (by norm_num : (1 : ℝ) / 2 ≤ 1)
      (fun η hη hηsmall => hopen η hη (by linarith))

end PoincareConjecture.M76
