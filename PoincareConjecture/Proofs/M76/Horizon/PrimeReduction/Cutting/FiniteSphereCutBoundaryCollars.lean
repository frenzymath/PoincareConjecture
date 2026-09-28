import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.SphereCutBoundaryCollar
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.SphereCutPLDomain
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.FiniteCutPLDomain
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.FiniteSphereBicollars

set_option autoImplicit false
set_option maxHeartbeats 1400000

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "J" => Icc (-1 : ℝ) 1
local notation "I" => Icc (0 : ℝ) 1

theorem exists_finite_sphere_cut_boundary_collars
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X]
    {E : κ → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)] [∀ i, FiniteDimensional ℝ (E i)]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (N : ∀ i, SimplicialComplex ℝ (E i)) (c : ∀ i, E i × ℝ → X) (δ : κ → ℝ)
    (hdata : ∀ i, (N i).faces.Finite ∧
      PolyhedralPLInCharts e (c i) ((N i).space ×ˢ J) ∧
      Topology.IsEmbedding (fun z : ((N i).space ×ˢ J : Set (E i × ℝ)) => c i z) ∧
      0 < δ i ∧ δ i ≤ 1 ∧
      MapsTo (c i) ((N i).space ×ˢ Icc (-δ i) (δ i)) (interior R) ∧
      IsOpen (c i '' ((N i).space ×ˢ Ioo (-δ i) (δ i))))
    (hdis : Pairwise fun i j =>
      Disjoint (c i '' ((N i).space ×ˢ Icc (-δ i) (δ i)))
        (c j '' ((N j).space ×ˢ Icc (-δ j) (δ j)))) :
    ∃ d : ∀ i, Bool → E i × ℝ → X,
      (∀ i b x r, d i b (x, r) = c i (x,
        if b then δ i / 2 + (δ i - δ i / 2) * r else -(δ i / 2 + (δ i - δ i / 2) * r))) ∧
      let Q := R \ ⋃ i, c i '' ((N i).space ×ˢ Ioo (-(δ i / 2)) (δ i / 2))
      ∀ i b, PolyhedralPLInCharts e (d i b) ((N i).space ×ˢ I) ∧
        Topology.IsEmbedding (fun z : ((N i).space ×ˢ I : Set (E i × ℝ)) => d i b z) ∧
        MapsTo (d i b) ((N i).space ×ˢ I) Q ∧
        MapsTo (d i b) ((N i).space ×ˢ I)
          (c i '' ((N i).space ×ˢ Icc (-δ i) (δ i))) ∧
        (∀ x, d i b (x, 0) = c i (x, if b then δ i / 2 else -(δ i / 2))) ∧
        (∀ z ∈ (N i).space ×ˢ I,
          d i b z ∈ c i '' ((N i).space ×ˢ
            ({if b then δ i / 2 else -(δ i / 2)} : Set ℝ)) ↔ z.2 = 0) ∧
        ∀ η : ℝ, 0 < η → η < 1 →
          IsOpen ((Subtype.val : Q → X) ⁻¹' (d i b '' ((N i).space ×ˢ Ico 0 η))) := by
  classical
  have hex (i : κ) := exists_sphere_cut_boundary_collars (N i) (hdata i).1 (c i)
    (hdata i).2.1 (hdata i).2.2.1
    (by linarith [(hdata i).2.2.2.1] : 0 < δ i / 2)
    (by linarith [(hdata i).2.2.2.1] : δ i / 2 < δ i)
    (hdata i).2.2.2.2.1 (hdata i).2.2.2.2.2.1 (hdata i).2.2.2.2.2.2
  choose d hd hsingle using hex
  let O : κ → Set X := fun i => c i '' ((N i).space ×ˢ Ioo (-(δ i / 2)) (δ i / 2))
  let C : κ → Set X := fun i => c i '' ((N i).space ×ˢ Icc (-δ i) (δ i))
  let Q := R \ ⋃ i, O i
  have hOC (i : κ) : O i ⊆ C i := by
    apply image_mono
    rintro ⟨x, r⟩ ⟨hx, hr⟩
    exact ⟨hx, by constructor <;> linarith [hr.1, hr.2, (hdata i).2.2.2.1]⟩
  refine ⟨d, hd, ?_⟩
  dsimp only
  intro i b
  obtain ⟨hPL, hci, hQi, hbase, hzero, hopen⟩ := hsingle i b
  have houter : MapsTo (d i b) ((N i).space ×ˢ I) (C i) := by
    rintro ⟨x, r⟩ ⟨hx, hr⟩
    rw [hd]
    refine ⟨(x, if b then δ i / 2 + (δ i - δ i / 2) * r
      else -(δ i / 2 + (δ i - δ i / 2) * r)), ⟨hx, ?_⟩, rfl⟩
    have hpos : 0 < δ i := (hdata i).2.2.2.1
    have hlo : δ i / 2 ≤ δ i / 2 + (δ i - δ i / 2) * r := by nlinarith [hr.1]
    have hhi : δ i / 2 + (δ i - δ i / 2) * r ≤ δ i := by nlinarith [hr.2]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> constructor <;> linarith
  have hQmap : MapsTo (d i b) ((N i).space ×ˢ I) Q := by
    intro z hz
    refine ⟨(hQi hz).1, ?_⟩
    intro hxO
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hxO
    by_cases hij : i = j
    · subst j
      exact (hQi hz).2 hxj
    · exact disjoint_left.mp (hdis hij) (houter hz) (hOC j hxj)
  refine ⟨hPL, hci, hQmap, houter, hbase, hzero, ?_⟩
  intro η hη hηone
  have hsub : Q ⊆ R \ O i := by
    intro x hx
    exact ⟨hx.1, fun hi => hx.2 (mem_iUnion.mpr ⟨i, hi⟩)⟩
  exact (hopen η hη hηone).preimage (continuous_inclusion hsub)

theorem exists_original_finite_cut_boundary_collars
    {X ι κ : Type*} [MetricSpace X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3} {R U : Set X}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hR : IsCompact R) (he : PLDomain e R)
    (hSR : ∀ i, S i ⊆ interior R) (hU : IsOpen U) (hSU : ∀ i, S i ⊆ U) :
    ∃ (t : κ → Finset R) (F : ∀ i, X → (t i → ℝ × V3))
      (N : ∀ i, SimplicialComplex ℝ (t i → ℝ × V3))
      (HB : ∀ i, (N i).space ≃ₜ S i)
      (c : ∀ i, (t i → ℝ × V3) × ℝ → X) (δ : κ → ℝ),
      (∀ i, Continuous (F i) ∧
        (∀ j, LocallyPiecewiseAffineOn (F i ∘ (e j).symm) (e j).target) ∧
        InjOn (F i) R ∧ (N i).space = F i '' S i) ∧
      (∀ i, (N i).faces.Finite ∧
        PolyhedralPLInCharts e (c i) ((N i).space ×ˢ J) ∧
        Topology.IsEmbedding (fun z : ((N i).space ×ˢ J :
          Set ((t i → ℝ × V3) × ℝ)) => c i z) ∧
        MapsTo (c i) ((N i).space ×ˢ J) R ∧
        (∀ x : (N i).space, c i ((x : t i → ℝ × V3), 0) = HB i x) ∧
        (∀ z : ((N i).space ×ˢ J : Set ((t i → ℝ × V3) × ℝ)),
          c i z ∈ S i ↔ (z : (t i → ℝ × V3) × ℝ).2 = 0) ∧
        0 < δ i ∧ δ i ≤ 1 / 2 ∧
        MapsTo (c i) ((N i).space ×ˢ Icc (-δ i) (δ i)) (U ∩ interior R) ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ δ i →
          IsOpen (c i '' ((N i).space ×ˢ Ioo (-ε) ε))) ∧
      Pairwise (fun i j =>
        Disjoint (c i '' ((N i).space ×ˢ Icc (-δ i) (δ i)))
          (c j '' ((N j).space ×ˢ Icc (-δ j) (δ j)))) ∧
      ∃ d : ∀ i, Bool → (t i → ℝ × V3) × ℝ → X,
        (∀ i b x r, d i b (x, r) = c i (x,
          if b then δ i / 2 + (δ i - δ i / 2) * r else -(δ i / 2 + (δ i - δ i / 2) * r))) ∧
        let Q := R \ ⋃ i, c i '' ((N i).space ×ˢ Ioo (-(δ i / 2)) (δ i / 2))
        IsCompact Q ∧ PLDomain e Q ∧
        ∀ i b, PolyhedralPLInCharts e (d i b) ((N i).space ×ˢ I) ∧
          Topology.IsEmbedding (fun z : ((N i).space ×ˢ I :
            Set ((t i → ℝ × V3) × ℝ)) => d i b z) ∧
          MapsTo (d i b) ((N i).space ×ˢ I) Q ∧
          MapsTo (d i b) ((N i).space ×ˢ I)
            (c i '' ((N i).space ×ˢ Icc (-δ i) (δ i))) ∧
          (∀ x, d i b (x, 0) = c i (x, if b then δ i / 2 else -(δ i / 2))) ∧
          (∀ z ∈ (N i).space ×ˢ I,
            d i b z ∈ c i '' ((N i).space ×ˢ
              ({if b then δ i / 2 else -(δ i / 2)} : Set ℝ)) ↔ z.2 = 0) ∧
          ∀ η : ℝ, 0 < η → η < 1 →
            IsOpen ((Subtype.val : Q → X) ⁻¹' (d i b '' ((N i).space ×ˢ Ico 0 η))) := by
  classical
  obtain ⟨t, F, N, HB, c, δ, hFmodel, hmodel, hdisjoint⟩ :=
    exists_original_finite_sphere_bicollars_with_model S sS hdis hR he hSR hU hSU
  have hdata : ∀ i, (N i).faces.Finite ∧
      PolyhedralPLInCharts e (c i) ((N i).space ×ˢ J) ∧
      Topology.IsEmbedding (fun z : ((N i).space ×ˢ J :
        Set ((t i → ℝ × V3) × ℝ)) => c i z) ∧
      0 < δ i ∧ δ i ≤ 1 ∧
      MapsTo (c i) ((N i).space ×ˢ Icc (-δ i) (δ i)) (interior R) ∧
      IsOpen (c i '' ((N i).space ×ˢ Ioo (-δ i) (δ i))) := by
    intro i
    obtain ⟨hN, hPL, hc, _, _, _, hd, hds, hi, ho⟩ := hmodel i
    exact ⟨hN, hPL, hc, hd, by linarith, fun _ hz => (hi hz).2, ho (δ i) hd le_rfl⟩
  obtain ⟨d, hd, hddata⟩ := exists_finite_sphere_cut_boundary_collars N c δ hdata hdisjoint
  let O : κ → Set X := fun i => c i '' ((N i).space ×ˢ Ioo (-(δ i / 2)) (δ i / 2))
  have hhalf (i : κ) : 0 < δ i / 2 ∧ δ i / 2 < δ i := by
    constructor <;> linarith [(hdata i).2.2.2.1]
  have hO (i : κ) : IsOpen (O i) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, ho⟩ := hmodel i
    exact ho (δ i / 2) (hhalf i).1 (hhalf i).2.le
  have hclosure (i : κ) : closure (O i) =
      c i '' ((N i).space ×ˢ Icc (-(δ i / 2)) (δ i / 2)) :=
    (hdata i).2.1.continuousOn.closure_image_collar_strip
      ((N i).isCompact_space_of_finite (hdata i).1) (hhalf i).1
      ((hhalf i).2.le.trans (hdata i).2.2.2.2.1)
  have hsmall (i : κ) : (N i).space ×ˢ Icc (-(δ i / 2)) (δ i / 2) ⊆
      (N i).space ×ˢ Icc (-δ i) (δ i) := by
    rintro ⟨x, r⟩ ⟨hx, hr⟩
    exact ⟨hx, by constructor <;> linarith [hr.1, hr.2, (hdata i).2.2.2.1]⟩
  have hclosedInside (i : κ) : closure (O i) ⊆ interior R := by
    rw [hclosure i]
    rintro _ ⟨z, hz, rfl⟩
    exact (hdata i).2.2.2.2.2.1 (hsmall i hz)
  have hclosedDisjoint : Pairwise fun i j => Disjoint (closure (O i)) (closure (O j)) := by
    intro i j hij
    rw [hclosure i, hclosure j]
    exact (hdisjoint hij).mono (image_mono (hsmall i)) (image_mono (hsmall j))
  have hcut (i : κ) : PLDomain e (R \ O i) := by
    obtain ⟨_, hF, hFi, hNs⟩ := hFmodel i
    exact (sS i).plDomain_bicollar_cut hR he (F i) hF
      (hFi.mono ((hSR i).trans interior_subset)) hNs
      ((N i).isCompact_space_of_finite (hdata i).1) (c i) (hdata i).2.1 (hdata i).2.2.1
      (hhalf i).1 (hhalf i).2 (hdata i).2.2.2.2.1 (hdata i).2.2.2.2.2.1 (hO i)
  have hcompact := (finite_collar_cut_geometry hR hO hclosedInside hclosedDisjoint).1
  have hPL := he.sdiff_iUnion_of_disjoint_collar_closures hR hO hclosedInside hclosedDisjoint hcut
  exact ⟨t, F, N, HB, c, δ, hFmodel, hmodel, hdisjoint, d, hd, hcompact, hPL, hddata⟩

end PoincareConjecture.M76
