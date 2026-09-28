import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.OriginalCollaredSphereCaps
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.Charts.OpenCarrierChartRestriction
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.Charts.FiniteCappedCarrierPointCharts

set_option autoImplicit false

open Set Metric Geometry Geometry.SeparatedSphereCaps

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "J" => Icc (-1 : ℝ) 1



theorem exists_original_capped_interior_atlas
    {X ι κ : Type*} [MetricSpace X] [Fintype κ] [DecidableEq κ]
    {e : ι → OpenPartialHomeomorph X V3} {R U : Set X}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hR : IsCompact R) (he : PLDomain e R)
    (hSR : ∀ i, S i ⊆ interior R) (hU : IsOpen U) (hSU : ∀ i, S i ⊆ U) :
    ∃ (t₀ : κ → Finset R)
      (N : ∀ i, SimplicialComplex ℝ (t₀ i → ℝ × V3))
      (HB : ∀ i, (N i).space ≃ₜ S i)
      (c : ∀ i, (t₀ i → ℝ × V3) × ℝ → X) (δ : κ → ℝ),
      let Q := R \ ⋃ i, c i '' ((N i).space ×ˢ Ioo (-(δ i / 2)) (δ i / 2))
      let B : κ × Bool → Set X := fun b => c b.1 '' ((N b.1).space ×ˢ
        ({if b.2 then δ b.1 / 2 else -(δ b.1 / 2)} : Set ℝ))
      ∃ (H : ∀ b, S b.1 ≃ₜ B b) (_sB : ∀ b, ChartwisePLSphere e (B b))
        (t : Finset Q) (F : X → (t → ℝ × V3))
        (K : SimplicialComplex ℝ (t → ℝ × V3)) (HQ : Q ≃ₜ K.space)
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
        (∀ b (x : S b.1), (H b x : X) =
          c b.1 (((HB b.1).symm x : t₀ b.1 → ℝ × V3),
            if b.2 then δ b.1 / 2 else -(δ b.1 / 2))) ∧
        IsCompact Q ∧ PLDomain e Q ∧
        frontier Q = frontier R ∪ ⋃ b, B b ∧
        Pairwise (fun b a => Disjoint (B b) (B a)) ∧
        (⋃ b, B b) ⊆ U ∩ interior R ∧
        frontier R ⊆ Q ∧ Q \ U = R \ U ∧ Disjoint (⋃ i, S i) Q ∧
        Continuous F ∧
        (∀ j, LocallyPiecewiseAffineOn (F ∘ (e j).symm) (e j).target) ∧
        InjOn F Q ∧ K.faces.Finite ∧ K.space = F '' Q ∧
        (∀ x : Q, (HQ x : t → ℝ × V3) = F x) ∧
        (∀ x ∈ Q, ∃ (j : ι) (V : Set X) (a : (t → ℝ × V3) →ᴬ[ℝ] V3),
          IsOpen V ∧ x ∈ V ∧ V ⊆ (e j).source ∧ EqOn (a ∘ F) (e j) V) ∧
        (∀ b, IsFinitePLBallPair V3 (cap b (F '' B b)) (lift '' (F '' B b))) ∧
        (∀ b, cap b (F '' B b) ∩ lift '' K.space = lift '' (F '' B b)) ∧
        Pairwise (fun b a => Disjoint (cap b (F '' B b)) (cap a (F '' B a))) ∧
        Disjoint (lift '' (F '' frontier R)) (⋃ b, cap b (F '' B b)) ∧
        C.faces.Finite ∧ C.space = lift '' K.space ∪ ⋃ b, cap b (F '' B b) ∧
        let W := C.space \ lift '' (F '' frontier R)
        ∃ atlas : W → OpenPartialHomeomorph W V3,
          (∀ p : W, p ∈ (atlas p).source) ∧ PLDomain atlas Set.univ ∧
          ∀ p : W, ∃ (A : Set ((t → ℝ × V3) × ((κ × Bool) → ℝ)))
            (f : ((t → ℝ × V3) × ((κ × Bool) → ℝ)) → V3)
            (g : V3 → ((t → ℝ × V3) × ((κ × Bool) → ℝ))),
            FinitePiecewiseAffineOn f A ∧
            FinitePiecewiseAffineOn g (closedBall (0 : V3) 1) ∧
            (∀ x ∈ (atlas p).source, (x : (t → ℝ × V3) × ((κ × Bool) → ℝ)) ∈ A ∧
              atlas p x = f x) ∧
            (atlas p).target ⊆ interior (closedBall (0 : V3) 1) ∧
            ∀ y ∈ (atlas p).target,
              ((atlas p).symm y : (t → ℝ × V3) × ((κ × Bool) → ℝ)) = g y := by
  classical
  obtain ⟨t₀, N, HB, c, δ, d, PB, sB, t, F, K, L, HQ, C,
    hmodel, hOopen, hclosedDisjoint, hd, hPB, hQ, hQPL, hQfront, hBdis, hBins,
    hfinite, hPcompact, hcollars⟩ :=
    exists_original_collared_sphere_caps S sS hdis hR he hSR hU hSU
  let Q := R \ ⋃ i, c i '' ((N i).space ×ˢ Ioo (-(δ i / 2)) (δ i / 2))
  let B : κ × Bool → Set X := fun b => c b.1 '' ((N b.1).space ×ˢ
    ({if b.2 then δ b.1 / 2 else -(δ b.1 / 2)} : Set ℝ))
  obtain ⟨hFc, hF, hFi, hK, _, _, hKs, _, hHQ, _, _, hproj, _, _,
    hball, hattach, hcapDis, hC, hCs⟩ := hfinite
  let H : ∀ b, S b.1 ≃ₜ B b := fun b => (HB b.1).symm.trans (PB b)
  have hHmark (b : κ × Bool) (x : S b.1) :
      (H b x : X) = c b.1 (((HB b.1).symm x : t₀ b.1 → ℝ × V3),
        if b.2 then δ b.1 / 2 else -(δ b.1 / 2)) := hPB b ((HB b.1).symm x)
  have hold : frontier R ⊆ Q := by
    intro x hx
    apply hQ.isClosed.frontier_subset
    rw [hQfront]
    exact Or.inl hx
  have hstripU (i : κ) :
      c i '' ((N i).space ×ˢ Ioo (-(δ i / 2)) (δ i / 2)) ⊆ U := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨_, _, _, _, hδ, _, hinside⟩ := hmodel i
    exact (hinside ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩).1
  have houtside : Q \ U = R \ U := by
    ext x
    constructor
    · exact fun hx => ⟨hx.1.1, hx.2⟩
    · intro hx
      refine ⟨⟨hx.1, ?_⟩, hx.2⟩
      intro hi
      obtain ⟨i, hi⟩ := mem_iUnion.mp hi
      exact hx.2 (hstripU i hi)
  have hSQ : Disjoint (⋃ i, S i) Q := by
    apply disjoint_left.mpr
    intro x hx hqx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    let y := (HB i).symm ⟨x, hxi⟩
    obtain ⟨_, _, _, hc0, hδ, _, _⟩ := hmodel i
    apply hqx.2
    exact mem_iUnion.mpr ⟨i, ⟨((y : t₀ i → ℝ × V3), 0),
      ⟨y.property, by constructor <;> linarith⟩,
      (hc0 y).trans (congrArg Subtype.val ((HB i).apply_symm_apply ⟨x, hxi⟩))⟩⟩
  let E := (t → ℝ × V3) × ((κ × Bool) → ℝ)
  let P : Set E := lift '' K.space
  let caps : κ × Bool → Set E := fun b => cap b (F '' B b)
  let bases : κ × Bool → Set E := fun b => lift '' (F '' B b)
  let Z : Set E := lift '' (F '' frontier R)
  let T : Set E := P ∪ ⋃ b, caps b
  let W : Set E := C.space \ Z
  have hBsub (b : κ × Bool) : B b ⊆ Q := by
    intro x hx
    apply hQ.isClosed.frontier_subset
    rw [hQfront]
    exact Or.inr (mem_iUnion.mpr ⟨b, hx⟩)
  have hZdis : Disjoint Z (⋃ b, caps b) := by
    apply disjoint_left.mpr
    rintro z ⟨_, ⟨x, hx, rfl⟩, rfl⟩ hz
    obtain ⟨b, hb⟩ := mem_iUnion.mp hz
    have hxK : F x ∈ K.space := hKs.symm ▸ mem_image_of_mem F (hold hx)
    have hxbase := (hattach b).subset ⟨hb, mem_image_of_mem lift hxK⟩
    obtain ⟨_, ⟨y, hy, rfl⟩, hxy⟩ := hxbase
    have hyx : y = x := hFi (hBsub b hy) (hold hx) (congrArg Prod.fst hxy)
    exact hx.2 (hBins (mem_iUnion.mpr ⟨b, hyx ▸ hy⟩)).2
  let FL : X → E := fun x => lift (F x)
  let aL : (t → ℝ × V3) →ᴬ[ℝ] E :=
    (ContinuousAffineMap.id ℝ _).prod (ContinuousAffineMap.const ℝ _ 0)
  have haL : FinitePiecewiseAffineOn aL K.space :=
    ⟨K, hK, rfl, K.affineOnFaces_affine aL⟩
  obtain ⟨HL, _, hHL⟩ := haL.exists_homeomorph_image
    (fun _ _ _ _ h => congrArg Prod.fst h)
  let HP : Q ≃ₜ P := HQ.trans HL
  have hHP (x : Q) : (HP x : E) = FL x := by
    change (HL (HQ x) : E) = _
    rw [hHL, hHQ]
    rfl
  have hFL : ∀ j, LocallyPiecewiseAffineOn (FL ∘ (e j).symm) (e j).target := by
    intro j
    exact (hF j).prod_mk (locallyPiecewiseAffineOn_affine
      (ContinuousAffineMap.const ℝ V3 (0 : (κ × Bool) → ℝ)) (e j).open_target)
  have hFLi : InjOn FL Q := fun x hx y hy h => hFi hx hy (congrArg Prod.fst h)
  have hZclosed : IsClosed Z := by
    have hfront := hR.of_isClosed_subset isClosed_frontier hR.isClosed.frontier_subset
    exact ((hfront.image hFc).image
      (continuous_id.prodMk continuous_const : Continuous (lift : (t → ℝ × V3) → E))).isClosed
  have hboundary : FL '' frontier Q ⊆ Z ∪ ⋃ b, bases b := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hQfront] at hx
    rcases hx with hx | hx
    · exact Or.inl (mem_image_of_mem lift (mem_image_of_mem F hx))
    · obtain ⟨b, hb⟩ := mem_iUnion.mp hx
      exact Or.inr (mem_iUnion.mpr ⟨b, mem_image_of_mem lift (mem_image_of_mem F hb)⟩)
  have hWT : W ⊆ T := fun _ hx => hCs.subset hx.1
  have hWopen : IsOpen ((Subtype.val : T → E) ⁻¹' W) := by
    have heq : (Subtype.val : T → E) ⁻¹' W =
        ((Subtype.val : T → E) ⁻¹' Z)ᶜ := by
      ext x
      exact and_iff_right (hCs.symm.subset x.property)
    rw [heq]
    exact (hZclosed.preimage continuous_subtype_val).isOpen_compl
  have hcol : ∀ b, ∃ (g : E × ℝ → E)
      (G : (bases b ×ˢ Icc (0 : ℝ) 1 : Set (E × ℝ)) ≃ₜ
        g '' (bases b ×ˢ Icc (0 : ℝ) 1)),
      G.IsFinitePL ∧ (∀ z, (G z : E) = g z) ∧
      MapsTo g (bases b ×ˢ Icc (0 : ℝ) 1) P ∧
      (∀ x ∈ bases b, g (x, 0) = x) ∧
      (∀ z ∈ bases b ×ˢ Icc (0 : ℝ) 1, g z ∈ bases b ↔ z.2 = 0) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        IsOpen ((Subtype.val : P → E) ⁻¹' (g '' (bases b ×ˢ Ico 0 ε))) := by
    intro b
    obtain ⟨g, G, hG, hGv, hgP, hg0, hgB, _, hgopen⟩ := hcollars b
    exact ⟨g, G, hG, hGv, hgP, hg0, hgB, hgopen⟩
  have hpoint (p : W) := exists_finite_capped_carrier_point_chart
    hQPL FL hFL hFLi HP hHP hPcompact.isClosed caps bases
    (fun b => (hball b).isCompact.isClosed) hcapDis hball
    (fun b => (inter_comm P (caps b)).trans (hattach b)) hboundary hcol
    ⟨p, hWT p.property⟩ p.property.2
  choose A charts f g hAT hpchart hsource htarget hf hg hforward hinverse using hpoint
  obtain ⟨atlas, hcenter, hcompat, hsources, htargets, hforwards, hinverses⟩ :=
    OpenPartialHomeomorph.exists_compatible_open_carrier_charts
      hWT hWopen charts A (fun _ => closedBall (0 : V3) 1) f g
      hpchart hf hg hsource htarget hforward hinverse
  have hatlas : PLDomain atlas Set.univ := by
    refine ⟨(fun x => ⟨x, hcenter x⟩), hcompat, isClosed_univ, ?_⟩
    simp
  refine ⟨t₀, N, HB, c, δ, H, sB, t, F, K, HQ, C, hmodel, hOopen, hclosedDisjoint, hHmark,
    hQ, hQPL, hQfront, hBdis, hBins, hold, houtside, hSQ,
    hFc, hF, hFi, hK, hKs, hHQ, hproj, hball, hattach, hcapDis, hZdis,
    hC, hCs, atlas, hcenter, hatlas, ?_⟩
  intro p
  refine ⟨A p, f p, g p, hf p, hg p, ?_, ?_, hinverses p⟩
  · intro x hx
    exact ⟨hsource p _ ((hsources p) ▸ hx), hforwards p x hx⟩
  · intro y hy
    exact htarget p (((htargets p) ▸ hy).1)

end PoincareConjecture.M76
