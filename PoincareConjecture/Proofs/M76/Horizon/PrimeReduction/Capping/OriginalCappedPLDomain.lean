import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.OriginalCappedInteriorAtlas
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.NestedFiniteSphereCut
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.MarkedCutOfOriginalCollars

import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.NestedCappedDomain
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.MarkedCapAvoidance
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.OriginalCappedAtlasAvoidance
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.OriginalRetainedSphereDescent
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.RetainedBallTransport

set_option autoImplicit false
set_option maxHeartbeats 1200000

open Set Metric Geometry Geometry.SeparatedSphereCaps

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "J" => Icc (-1 : ℝ) 1







theorem exists_original_capped_pl_domain
    {X ι κ : Type*} [MetricSpace X] [Fintype κ] [DecidableEq κ]
    {e : ι → OpenPartialHomeomorph X V3} {R U : Set X}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hR : IsCompact R) (he : PLDomain e R)
    (hSR : ∀ i, S i ⊆ interior R) (hU : IsOpen U) (hSU : ∀ i, S i ⊆ U) :
    ∃ P : Set X, IsCompact P ∧ R ⊆ interior P ∧ PLDomain e P ∧
    ∃ (t₀ : κ → Finset P)
      (N : ∀ i, SimplicialComplex ℝ (t₀ i → ℝ × V3))
      (HB : ∀ i, (N i).space ≃ₜ S i)
      (c : ∀ i, (t₀ i → ℝ × V3) × ℝ → X) (δ : κ → ℝ),
      let O := ⋃ i, c i '' ((N i).space ×ˢ Ioo (-(δ i / 2)) (δ i / 2))
      let Qouter := P \ O
      let Qinner := R \ O
      let B : κ × Bool → Set X := fun b => c b.1 '' ((N b.1).space ×ˢ
        ({if b.2 then δ b.1 / 2 else -(δ b.1 / 2)} : Set ℝ))
      ∃ (H : ∀ b, S b.1 ≃ₜ B b) (_sB : ∀ b, ChartwisePLSphere e (B b))
        (t : Finset Qouter) (F : X → (t → ℝ × V3))
        (K : SimplicialComplex ℝ (t → ℝ × V3)) (HQ : Qouter ≃ₜ K.space)
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
        IsOpen O ∧ closure O ⊆ U ∩ interior R ∧
        IsCompact Qouter ∧ PLDomain e Qouter ∧
        frontier Qouter = frontier P ∪ ⋃ b, B b ∧
        IsCompact Qinner ∧ PLDomain e Qinner ∧
        frontier Qinner = frontier R ∪ ⋃ b, B b ∧
        Pairwise (fun b a => Disjoint (B b) (B a)) ∧
        (⋃ b, B b) ⊆ U ∩ interior R ∧
        frontier P ⊆ Qouter ∧ frontier R ⊆ Qinner ∧
        Qouter \ U = P \ U ∧ Qinner \ U = R \ U ∧
        Disjoint (⋃ i, S i) Qouter ∧
        Continuous F ∧
        (∀ j, LocallyPiecewiseAffineOn (F ∘ (e j).symm) (e j).target) ∧
        InjOn F Qouter ∧ K.faces.Finite ∧ K.space = F '' Qouter ∧
        (∀ x : Qouter, (HQ x : t → ℝ × V3) = F x) ∧
        (∀ x ∈ Qouter, ∃ (j : ι) (V : Set X) (a : (t → ℝ × V3) →ᴬ[ℝ] V3),
          IsOpen V ∧ x ∈ V ∧ V ⊆ (e j).source ∧ EqOn (a ∘ F) (e j) V) ∧
        (∀ b, IsFinitePLBallPair V3 (cap b (F '' B b)) (lift '' (F '' B b))) ∧
        (∀ b, cap b (F '' B b) ∩ lift '' K.space = lift '' (F '' B b)) ∧
        Pairwise (fun b a => Disjoint (cap b (F '' B b)) (cap a (F '' B a))) ∧
        Disjoint (lift '' (F '' frontier P)) (⋃ b, cap b (F '' B b)) ∧
        Disjoint (lift '' (F '' frontier R)) (⋃ b, cap b (F '' B b)) ∧
        Disjoint (lift '' (F '' (R \ U))) (⋃ b, cap b (F '' B b)) ∧
        C.faces.Finite ∧ C.space = lift '' K.space ∪ ⋃ b, cap b (F '' B b) ∧
        let W := C.space \ lift '' (F '' frontier P)
        let D := lift '' (F '' Qinner) ∪ ⋃ b, cap b (F '' B b)
        D ⊆ W ∧
        ∃ cut : MarkedSphereCut e R κ,
          cut.spheres = S ∧
          cut.collar = (fun i => c i '' ((N i).space ×ˢ Ioo (-(δ i / 2)) (δ i / 2))) ∧
          cut.ports = B ∧ HEq cut.portMap H ∧
        ∃ atlas : W → OpenPartialHomeomorph W V3,
          (∀ p : W, p ∈ (atlas p).source) ∧ PLDomain atlas Set.univ ∧
          (∀ p : W, ∃ (A : Set ((t → ℝ × V3) × ((κ × Bool) → ℝ)))
            (f : ((t → ℝ × V3) × ((κ × Bool) → ℝ)) → V3)
            (g : V3 → ((t → ℝ × V3) × ((κ × Bool) → ℝ))),
            FinitePiecewiseAffineOn f A ∧
            FinitePiecewiseAffineOn g (closedBall (0 : V3) 1) ∧
            (∀ x ∈ (atlas p).source, (x : (t → ℝ × V3) × ((κ × Bool) → ℝ)) ∈ A ∧
              atlas p x = f x) ∧
            (atlas p).target ⊆ interior (closedBall (0 : V3) 1) ∧
            ∀ y ∈ (atlas p).target,
              ((atlas p).symm y : (t → ℝ × V3) × ((κ × Bool) → ℝ)) = g y) ∧
          PLDomain atlas ((Subtype.val : W → ((t → ℝ × V3) × ((κ × Bool) → ℝ))) ⁻¹' D) ∧
          IsCompact ((Subtype.val : W → ((t → ℝ × V3) × ((κ × Bool) → ℝ))) ⁻¹' D) ∧
          frontier ((Subtype.val : W → ((t → ℝ × V3) × ((κ × Bool) → ℝ))) ⁻¹' D) =
            (Subtype.val : W → ((t → ℝ × V3) × ((κ × Bool) → ℝ))) ⁻¹'
              (lift '' (F '' frontier R)) ∧
          (∀ b, Nonempty (ChartwisePLBall atlas
            ((Subtype.val : W → ((t → ℝ × V3) × ((κ × Bool) → ℝ))) ⁻¹' cap b (F '' B b))
            ((Subtype.val : W → ((t → ℝ × V3) × ((κ × Bool) → ℝ))) ⁻¹' lift '' (F '' B b)))) ∧
          (∀ b, (Subtype.val : W → ((t → ℝ × V3) × ((κ × Bool) → ℝ))) ⁻¹' cap b (F '' B b) ⊆
            interior ((Subtype.val : W → ((t → ℝ × V3) × ((κ × Bool) → ℝ))) ⁻¹' D)) ∧
          ∀ (S' : Set W), ChartwisePLSphere atlas S' → ∃ (G : W ≃ₜ W) (V : Set W),
            IsCompact V ∧ V ⊆ interior ((Subtype.val : W → ((t → ℝ × V3) × ((κ × Bool) → ℝ))) ⁻¹' D) ∧
            EqOn G id Vᶜ ∧
            (∀ i j, (atlas i).symm.trans (G.toOpenPartialHomeomorph.trans (atlas j)) ∈
              piecewiseAffineGroupoid V3) ∧
            (∀ i j, (atlas i).symm.trans (G.symm.toOpenPartialHomeomorph.trans (atlas j)) ∈
              piecewiseAffineGroupoid V3) ∧
            Nonempty (ChartwisePLSphere atlas (G '' S')) ∧
            Disjoint (G '' S') ((Subtype.val : W → ((t → ℝ × V3) × ((κ × Bool) → ℝ))) ⁻¹'
              ⋃ b, cap b (F '' B b)) ∧
            (S' ⊆ interior ((Subtype.val : W → ((t → ℝ × V3) × ((κ × Bool) → ℝ))) ⁻¹' D) →
              ∃ T : Set X, Nonempty (ChartwisePLSphere e T) ∧ T ⊆ interior Qinner ∧
                lift '' (F '' T) =
                  (Subtype.val : W → ((t → ℝ × V3) × ((κ × Bool) → ℝ))) '' (G '' S') ∧
                ((¬ ∃ A' : Set W,
                    A' ⊆ (Subtype.val : W → ((t → ℝ × V3) × ((κ × Bool) → ℝ))) ⁻¹' D ∧
                    Nonempty (ChartwisePLBall atlas A' S')) →
                  ¬ ∃ A : Set X, A ⊆ Qinner ∧ Nonempty (ChartwisePLBall e A T))) := by
  classical
  obtain ⟨P, hP, hRP, heP⟩ := he.exists_compact_ambient_neighborhood hR
  obtain ⟨t₀, N, HB, c, δ, H, sB, t, F, K, HQ, C,
    hmodel, hOopen, hclosedDisjoint, hmark, hQo, heQo, hQof, hBdis, hBins, hOldP, houtside,
    hSQ, hFc, hF, hFi, hK, hKs, hHQ, hproj, hball, hattach,
    hcapsdis, hOldPdis, hC, hCs, atlas, hcenter, hatlas, hrep⟩ :=
    exists_original_capped_interior_atlas S sS hdis hP heP
      (fun i => (hSR i).trans interior_subset |>.trans hRP)
      (hU.inter isOpen_interior) (fun i x hx => ⟨hSU i hx, hSR i hx⟩)
  let O := ⋃ i, c i '' ((N i).space ×ˢ Ioo (-(δ i / 2)) (δ i / 2))
  let Qo := P \ O
  let Qi := R \ O
  let B : κ × Bool → Set X := fun b => c b.1 '' ((N b.1).space ×ˢ
    ({if b.2 then δ b.1 / 2 else -(δ b.1 / 2)} : Set ℝ))
  have hinside (i : κ) :
      MapsTo (c i) ((N i).space ×ˢ Icc (-δ i) (δ i)) (U ∩ interior R) :=
    fun _ hz => ((hmodel i).2.2.2.2.2.2 hz).1
  obtain ⟨hO, hOcl, hBcl⟩ := finite_collar_removed_set_geometry
    t₀ N c δ (fun i => (hmodel i).1) (fun i => (hmodel i).2.1)
    (fun i => ⟨(hmodel i).2.2.2.2.1, (hmodel i).2.2.2.2.2.1⟩)
    hinside hRP heQo.closed
  have hOR : closure O ⊆ interior R := hOcl.trans inter_subset_right
  obtain ⟨heQi, hQi, hQeq, _, _, hQiPdis, hOldR, _, _⟩ :=
    he.nested_collar_cut hR hP hRP hO hOR heQo
  have hQiQo : Qi ⊆ Qo := fun _ hx => ⟨interior_subset (hRP hx.1), hx.2⟩
  have hBinside : (⋃ b, B b) ⊆ U ∩ interior R := hBins.trans inter_subset_left
  have hBQo (b : κ × Bool) : B b ⊆ Qo := by
    intro x hx
    apply heQo.closed.frontier_subset
    rw [hQof]
    exact Or.inr (mem_iUnion.mpr ⟨b, hx⟩)
  have hQif : frontier Qi = frontier R ∪ ⋃ b, B b := by
    change frontier (R \ O) = _
    rw [hQeq, frontier_inter_eq_of_closed he.closed heQo.closed, hQof]
    ext x
    constructor
    · rintro (⟨hx, _⟩ | ⟨hxR, hxP | hxB⟩)
      · exact Or.inl hx
      · exact False.elim (hxP.2 (hRP hxR))
      · exact Or.inr hxB
    · rintro (hx | hx)
      · exact Or.inl ⟨hx, hQiQo (hOldR hx)⟩
      · exact Or.inr ⟨interior_subset (hBinside hx).2, Or.inr hx⟩
  obtain ⟨cut, hcutS, hcutO, hcutB, hcutH⟩ :=
    exists_marked_sphere_cut_of_original_collars (fun i => t₀ i → ℝ × V3)
      S sS hdis hSR hR N (fun i => (hmodel i).1) HB c
      (fun i => (hmodel i).2.1) (fun i => (hmodel i).2.2.1)
      (fun i => (hmodel i).2.2.2.1) (fun i => δ i / 2)
      (fun i => half_pos (hmodel i).2.2.2.2.1)
      (fun i => by have := (hmodel i).2.2.2.2.2.1; linarith)
      hOopen (fun i => by
        rintro _ ⟨⟨x, r⟩, ⟨hx, hr⟩, rfl⟩
        apply (hinside i _).2
        refine ⟨hx, ?_⟩
        have := (hmodel i).2.2.2.2.1
        constructor <;> linarith [hr.1, hr.2])
      hclosedDisjoint B H sB hmark hBdis heQi hQif
  have hOU : O ⊆ U := subset_closure.trans (hOcl.trans inter_subset_left)
  have hQoU : Qo \ U = P \ U := by
    ext x
    constructor
    · exact fun hx => ⟨hx.1.1, hx.2⟩
    · exact fun hx => ⟨⟨hx.1, fun hn => hx.2 (hOU hn)⟩, hx.2⟩
  have hQiU : Qi \ U = R \ U := by
    ext x
    constructor
    · exact fun hx => ⟨hx.1.1, hx.2⟩
    · exact fun hx => ⟨⟨hx.1, fun hn => hx.2 (hOU hn)⟩, hx.2⟩
  let E := (t → ℝ × V3) × ((κ × Bool) → ℝ)
  let FL : X → E := fun x => lift (F x)
  let KL : Set E := lift '' K.space
  let caps : κ × Bool → Set E := fun b => cap b (F '' B b)
  let D : Set E := FL '' Qi ∪ ⋃ b, caps b
  let Z : Set E := lift '' (F '' frontier P)
  have hKL : KL = FL '' Qo := by
    change lift '' K.space = _
    rw [hKs, image_image]
  have hFLi : InjOn FL Qo := fun x hx y hy h => hFi hx hy (congrArg Prod.fst h)
  have hcapAttach (b : κ × Bool) : caps b ∩ KL = FL '' B b := by
    simpa only [caps, KL, FL, B, image_image] using hattach b
  have hcapAvoid (A : Set X) (hAQ : A ⊆ Qo) (hAB : Disjoint A (⋃ b, B b)) :
      Disjoint (FL '' A) (⋃ b, caps b) :=
    disjoint_model_image_caps FL B caps hFLi hKL hBQo hcapAttach hAQ hAB
  have hOldRdis : Disjoint (FL '' frontier R) (⋃ b, caps b) := by
    apply hcapAvoid (frontier R) (hOldR.trans hQiQo)
    exact disjoint_left.mpr (fun x hx hb => hx.2 (hBinside hb).2)
  have hOutsideDis : Disjoint (FL '' (R \ U)) (⋃ b, caps b) := by
    apply hcapAvoid (R \ U)
    · rw [← hQiU]
      exact sdiff_subset.trans hQiQo
    · exact disjoint_left.mpr (fun _ hx hb => hx.2 (hBinside hb).1)
  have hDZ : Disjoint D Z := by
    apply disjoint_left.mpr
    rintro y (⟨x, hx, rfl⟩ | hy) hz
    · obtain ⟨_, ⟨z, hzP, rfl⟩, hzx⟩ := hz
      have hzx' : z = x := hFLi (hOldP hzP) (hQiQo hx) hzx
      exact hzP.2 (hzx'.symm ▸ hRP hx.1)
    · exact disjoint_left.mp hOldPdis hz hy
  have hDT : D ⊆ KL ∪ ⋃ b, caps b := by
    apply union_subset
    · exact (image_mono hQiQo).trans (hKL.symm.subset.trans subset_union_left)
    · exact subset_union_right
  have hDW : D ⊆ C.space \ Z := by
    intro y hy
    exact ⟨hCs.symm.subset (hDT hy), fun hz => disjoint_left.mp hDZ hy hz⟩
  let aL : (t → ℝ × V3) →ᴬ[ℝ] E :=
    (ContinuousAffineMap.id ℝ _).prod (ContinuousAffineMap.const ℝ _ 0)
  have haL : FinitePiecewiseAffineOn aL K.space :=
    ⟨K, hK, rfl, K.affineOnFaces_affine aL⟩
  obtain ⟨HL, _, hHL⟩ := haL.exists_homeomorph_image
    (fun _ _ _ _ h => congrArg Prod.fst h)
  let Hmodel : Qo ≃ₜ KL := HQ.trans HL
  have hHmodel (x : Qo) : (Hmodel x : E) = FL x := by
    change (HL (HQ x) : E) = _
    rw [hHL, hHQ]
    rfl
  have hFL : ∀ j, LocallyPiecewiseAffineOn (FL ∘ (e j).symm) (e j).target := by
    intro j
    exact (hF j).prod_mk (locallyPiecewiseAffineOn_affine
      (ContinuousAffineMap.const ℝ V3 (0 : (κ × Bool) → ℝ)) (e j).open_target)
  have hKLclosed : IsClosed KL :=
    ((K.isCompact_space_of_finite hK).image
      (continuous_id.prodMk continuous_const : Continuous (lift : (t → ℝ × V3) → E))).isClosed
  have hCaps : IsCompact (⋃ b, caps b) := isCompact_iUnion (fun b => (hball b).isCompact)
  have hZclosed : IsClosed Z := by
    have hfront := hP.of_isClosed_subset isClosed_frontier hP.isClosed.frontier_subset
    exact ((hfront.image hFc).image
      (continuous_id.prodMk continuous_const : Continuous (lift : (t → ℝ × V3) → E))).isClosed
  have hAttachO : (⋃ b, caps b) ∩ KL ⊆ FL '' (closure O \ O) := by
    rintro y ⟨hy, hyK⟩
    obtain ⟨b, hb⟩ := mem_iUnion.mp hy
    obtain ⟨x, hx, rfl⟩ := (hcapAttach b).subset ⟨hb, hyK⟩
    exact ⟨x, ⟨hBcl b hx, (hBQo b hx).2⟩, rfl⟩
  have hconstructed :
      PLDomain atlas ((Subtype.val : (C.space \ Z : Set E) → E) ⁻¹' D) ∧
      IsCompact ((Subtype.val : (C.space \ Z : Set E) → E) ⁻¹' D) ∧
      frontier ((Subtype.val : (C.space \ Z : Set E) → E) ⁻¹' D) =
        (Subtype.val : (C.space \ Z : Set E) → E) ⁻¹' (FL '' frontier R) := by
    have hgeneral : ∀ (T : Set E), T = KL ∪ ⋃ b, caps b →
        ∀ (a : (T \ Z : Set E) → OpenPartialHomeomorph (T \ Z : Set E) V3),
        PLDomain a Set.univ →
        (∀ i, ∃ (A : Set E) (g : E → V3), FinitePiecewiseAffineOn g A ∧
          ∀ x ∈ (a i).source, (x : E) ∈ A ∧ a i x = g x) →
        PLDomain a ((Subtype.val : (T \ Z : Set E) → E) ⁻¹' D) ∧
        IsCompact ((Subtype.val : (T \ Z : Set E) → E) ⁻¹' D) ∧
        frontier ((Subtype.val : (T \ Z : Set E) → E) ⁻¹' D) =
          (Subtype.val : (T \ Z : Set E) → E) ⁻¹' (FL '' frontier R) := by
      intro T hT a ha hforward
      subst T
      exact he.nested_capped_domain hR hP hRP hO hOR heQo Hmodel FL hHmodel
        hFL hKLclosed hCaps hAttachO hZclosed hDZ a ha hforward
    apply hgeneral C.space hCs atlas hatlas
    intro i
    obtain ⟨A, f, g, hf, _, hforward, _, _⟩ := hrep i
    exact ⟨A, f, hf, hforward⟩
  have hcapCertificates := capped_atlas_balls_and_avoidance atlas
    hconstructed.1 hconstructed.2.1 hconstructed.2.2
    (fun i => by
      obtain ⟨A,f,_,hf,_,hforward,_,_⟩ := hrep i
      exact ⟨A,f,hf,hforward⟩)
    caps (fun b => lift '' (F '' B b)) hball
    (fun b => (show caps b ⊆ D from fun _ hx => Or.inr (mem_iUnion.mpr ⟨b,hx⟩)).trans hDW)
    (fun b _ hx => Or.inr (mem_iUnion.mpr ⟨b,hx⟩)) hcapsdis
    (by simpa only [caps,B,FL,image_image] using hOldRdis.symm)
  have hreturn (S' : Set (C.space \ Z : Set E)) (s' : ChartwisePLSphere atlas S') :
      ∃ (G : (C.space \ Z : Set E) ≃ₜ (C.space \ Z : Set E)) (V : Set (C.space \ Z : Set E)),
        IsCompact V ∧ V ⊆ interior ((Subtype.val : (C.space \ Z : Set E) → E) ⁻¹' D) ∧
        EqOn G id Vᶜ ∧
        (∀ i j, (atlas i).symm.trans (G.toOpenPartialHomeomorph.trans (atlas j)) ∈
          piecewiseAffineGroupoid V3) ∧
        (∀ i j, (atlas i).symm.trans (G.symm.toOpenPartialHomeomorph.trans (atlas j)) ∈
          piecewiseAffineGroupoid V3) ∧
        Nonempty (ChartwisePLSphere atlas (G '' S')) ∧
        Disjoint (G '' S') ((Subtype.val : (C.space \ Z : Set E) → E) ⁻¹' ⋃ b,caps b) ∧
        (S' ⊆ interior ((Subtype.val : (C.space \ Z : Set E) → E) ⁻¹' D) →
          ∃ T : Set X, Nonempty (ChartwisePLSphere e T) ∧ T ⊆ interior Qi ∧
            FL '' T = (Subtype.val : (C.space \ Z : Set E) → E) '' (G '' S') ∧
            ((¬ ∃ A' : Set (C.space \ Z : Set E),
                A' ⊆ (Subtype.val : (C.space \ Z : Set E) → E) ⁻¹' D ∧
                Nonempty (ChartwisePLBall atlas A' S')) →
              ¬ ∃ A : Set X, A ⊆ Qi ∧ Nonempty (ChartwisePLBall e A T))) := by
    obtain ⟨G,V,hV,hVD,hfix,hGPL,hGinv,⟨sG⟩,hclear⟩ := hcapCertificates.2.2 S' s'
    refine ⟨G,V,hV,hVD,hfix,hGPL,hGinv,⟨sG⟩,hclear,?_⟩
    intro hS'
    have hinside : G '' S' ⊆ interior ((Subtype.val : (C.space \ Z : Set E) → E) ⁻¹' D) := by
      rintro _ ⟨x,hx,rfl⟩
      by_contra hn
      have hfixed : G (G x) = G x := hfix (fun h => hn (hVD h))
      exact hn ((G.injective hfixed).symm ▸ hS' hx)
    have hret : G '' S' ⊆ (Subtype.val : (C.space \ Z : Set E) → E) ⁻¹' FL '' Qi := by
      intro x hx
      rcases interior_subset (hinside hx) with h | h
      · exact h
      · exact False.elim (disjoint_left.mp hclear hx h)
    obtain ⟨T,hT,hTQi,himage⟩ := exists_original_sphere_of_retained_model K hK HQ F hQiQo
      hHQ hproj atlas (fun i => by
        obtain ⟨_,_,g,_,hg,_,hgt,hgv⟩ := hrep i
        exact ⟨g,hg,hgt,hgv⟩) sG hret
    refine ⟨T,hT,?_,himage,?_⟩
    · intro x hx
      by_contra hn
      obtain ⟨y,hy,hyx⟩ := himage.subset (mem_image_of_mem FL hx)
      have hxfront : x ∈ frontier Qi := ⟨subset_closure (hTQi hx),hn⟩
      rcases hQif.subset hxfront with hxR | hxB
      · have hyfront : y ∈ frontier ((Subtype.val : (C.space \ Z : Set E) → E) ⁻¹' D) := by
          rw [hconstructed.2.2]
          change (y : E) ∈ FL '' frontier R
          exact hyx.symm ▸ mem_image_of_mem FL hxR
        exact hyfront.2 (hinside hy)
      · obtain ⟨b,hb⟩ := mem_iUnion.mp hxB
        have hcap : FL x ∈ caps b := ((hcapAttach b).symm.subset
          (mem_image_of_mem FL hb)).1
        apply disjoint_left.mp hclear hy
        change (y : E) ∈ ⋃ b,caps b
        exact hyx.symm ▸ mem_iUnion.mpr ⟨b,hcap⟩
    · rintro hno ⟨A,hA,⟨b⟩⟩
      apply hno
      exact exists_capped_ball_of_retained_ball b hA FL hFL (hFLi.mono hQiQo)
        subset_union_left hDW atlas hatlas.cover
        (fun i => by
          obtain ⟨A,f,_,hf,_,hforward,_,_⟩ := hrep i
          exact ⟨A,f,hf,hforward⟩)
        G hGinv (hVD.trans interior_subset) hfix himage
  refine ⟨P, hP, hRP, heP, t₀, N, HB, c, δ, H, sB, t, F, K, HQ, C,
    ?_, hOopen, hclosedDisjoint, hmark, hO, hOcl, hQo, heQo, hQof, hQi, heQi, hQif,
    hBdis, hBinside, hOldP, hOldR, hQoU, hQiU, hSQ,
    hFc, hF, hFi, hK, hKs, hHQ, hproj, hball, hattach, hcapsdis,
    hOldPdis, ?_, ?_, hC, hCs, ?_, cut, hcutS, hcutO, hcutB, hcutH,
    atlas, hcenter, hatlas, hrep, ?_⟩
  · intro i
    exact ⟨(hmodel i).1, (hmodel i).2.1, (hmodel i).2.2.1,
      (hmodel i).2.2.2.1, (hmodel i).2.2.2.2.1,
      (hmodel i).2.2.2.2.2.1, hinside i⟩
  · simpa only [FL, caps, B, image_image] using hOldRdis
  · simpa only [FL, caps, B, image_image] using hOutsideDis
  · simpa only [D, FL, Qi, O, caps, B, Z, image_image] using hDW
  · have hfull := And.intro hconstructed.1
      (And.intro hconstructed.2.1 (And.intro hconstructed.2.2
        (And.intro hcapCertificates.1 (And.intro hcapCertificates.2.1 hreturn))))
    simpa only [D, FL, Qi, O, caps, B, Z, image_image] using hfull

end PoincareConjecture.M76
