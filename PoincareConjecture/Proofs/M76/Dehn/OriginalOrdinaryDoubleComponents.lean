import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleSourcePolyhedron
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteTowerDescent
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.NestedFiniteCoordinateCubes
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TwoBranchWindows
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteClippedChartInverse
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLInitialSegment
import PoincareConjecture.Proofs.M76.Mathlib.RadialSegmentGerms
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteAffineCoverFaceBounds
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.IntrinsicAffineGerms
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedVertexIncidence
import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkCofaceCount
import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkDimension
import PoincareConjecture.Proofs.M76.Mathlib.LinkGraphIncidence
import PoincareConjecture.Proofs.M76.Mathlib.FiniteCarrierFaceInteriors

set_option autoImplicit false

open Set Metric Geometry Topology
open Filter
open scoped Topology
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1

variable {M ι : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}

theorem Step.exists_original_double_partner
    {s t : Stage e S f r C} (step : Step s t) {R Fmark : Set M}
    {base : Fmark} {Jgroup : Subgroup (FundamentalGroup Fmark base)}
    (new : StageMarkedDisk t R Fmark base Jgroup) :
    ∃ (L : SimplicialComplex ℝ (V2 × V2)) (G : SimplicialComplex ℝ V2)
      (first : L.space ≃ₜ G.space) (partner : G.space ≃ₜ G.space),
      L.faces.Finite ∧ G.faces.Finite ∧
      L.space = {z | z.1 ∈ D ∧ z.2 ∈ D ∧
        step.projection (step.inclusion (new.map z.1)) =
          step.projection (step.inclusion (new.map z.2)) ∧ z.1 ≠ z.2} ∧
      G.space = {x | x ∈ D ∧ ∃ y ∈ D, x ≠ y ∧
        step.projection (step.inclusion (new.map x)) =
          step.projection (step.inclusion (new.map y))} ∧
      first.IsFinitePL ∧ first.symm.IsFinitePL ∧
      (∀ z : L.space, (first z : V2) = z.val.1) ∧
      partner.IsFinitePL ∧ partner.symm.IsFinitePL ∧
      (∀ x : G.space, (partner x : V2) = (first.symm x).val.2) ∧
      Function.Involutive partner ∧ (∀ x : G.space, partner x ≠ x) ∧
      (∀ x : G.space,
        step.projection (step.inclusion (new.map x)) =
          step.projection (step.inclusion (new.map (partner x)))) ∧
      (∀ (x : G.space) (y : V2), y ∈ D → (x : V2) ≠ y →
        step.projection (step.inclusion (new.map x)) =
          step.projection (step.inclusion (new.map y)) → y = (partner x : V2)) ∧
      ∀ x : G.space, (partner x : V2) ∈ Rim ↔ (x : V2) ∈ Rim := by
  classical
  obtain ⟨K, hK, hKs⟩ := SimplicialComplex.exists_finite_coordinate_closedBall
    (0 : V2) (r := 1) zero_le_one
  have hj : PolyhedralPLInCharts t.charts new.map K.space := by
    simpa only [hKs] using new.piecewiseAffine
  have hji : IsEmbedding (fun x : K.space => new.map x) :=
    new.embedding.comp (Homeomorph.setCongr hKs).isEmbedding
  obtain ⟨L, G, first, hL, hG, hLs, hGs, hfirst, hfirstinv, hfirstval⟩ :=
    step.exists_finite_double_source_polyhedron K hK hj hji
  simp only [hKs] at hLs hGs
  have hswap (z : L.space) : z.val.swap ∈ L.space := by
    have hz := hLs.subset z.property
    exact hLs.symm.subset ⟨hz.2.1, hz.1, hz.2.2.1.symm, Ne.symm hz.2.2.2⟩
  let swap : L.space ≃ₜ L.space := {
    toFun := fun z => ⟨z.val.swap, hswap z⟩
    invFun := fun z => ⟨z.val.swap, hswap z⟩
    left_inv := fun z => Subtype.ext (Prod.swap_swap z.val)
    right_inv := fun z => Subtype.ext (Prod.swap_swap z.val)
    continuous_toFun :=
      (continuous_subtype_val.snd.prodMk continuous_subtype_val.fst).subtype_mk _
    continuous_invFun :=
      (continuous_subtype_val.snd.prodMk continuous_subtype_val.fst).subtype_mk _ }
  have hswapPL : swap.IsFinitePL := by
    let A := (ContinuousLinearEquiv.prodComm ℝ V2 V2).toContinuousLinearMap.toContinuousAffineMap
    exact ⟨Prod.swap, ⟨L, hL, rfl, L.affineOnFaces_affine A⟩, fun _ => rfl⟩
  let partner := first.symm.trans (swap.trans first)
  have hpartnerPL : partner.IsFinitePL := hfirstinv.trans (hswapPL.trans hfirst)
  have hfirstback (x : G.space) : (first.symm x).val.1 = (x : V2) := by
    rw [← hfirstval, first.apply_symm_apply]
  have hpartnerval (x : G.space) :
      (partner x : V2) = (first.symm x).val.2 := by
    exact hfirstval (swap (first.symm x))
  have hinvolution : Function.Involutive partner := by
    intro x
    apply first.symm.injective
    change first.symm (first (swap (first.symm (first (swap (first.symm x)))))) =
      first.symm x
    simp only [first.symm_apply_apply]
    exact Subtype.ext (Prod.swap_swap (first.symm x).val)
  have hnoFixed (x : G.space) : partner x ≠ x := by
    intro heq
    have hz := hLs.subset (first.symm x).property
    apply hz.2.2.2
    exact (hfirstback x).trans ((congrArg Subtype.val heq).symm.trans (hpartnerval x))
  have hvalue (x : G.space) :
      step.projection (step.inclusion (new.map x)) =
        step.projection (step.inclusion (new.map (partner x))) := by
    have hz := (hLs.subset (first.symm x).property).2.2.1
    rwa [hfirstback, ← hpartnerval] at hz
  refine ⟨L, G, first, partner, hL, hG, hLs, hGs, hfirst, hfirstinv,
    hfirstval, hpartnerPL, hpartnerPL.symm, hpartnerval, hinvolution, hnoFixed,
    hvalue, ?_, ?_⟩
  · intro x y hy hne heq
    let z : L.space := ⟨((x : V2), y),
      hLs.symm.subset ⟨(hGs.subset x.property).1, hy, heq, hne⟩⟩
    have hz : first z = x := Subtype.ext (hfirstval z)
    have hinv : first.symm x = z := by rw [← hz, first.symm_apply_apply]
    rw [hpartnerval, hinv]
  · intro x
    have hxD := (hGs.subset x.property).1
    have hyD := (hGs.subset (partner x).property).1
    rw [← new.whole_boundary_iff ⟨partner x, hyD⟩,
      ← new.whole_boundary_iff ⟨x, hxD⟩, step.frontier_preimage R]
    change step.projection (step.inclusion (new.map (partner x))) ∈
        frontier (s.projection ⁻¹' R) ↔
      step.projection (step.inclusion (new.map x)) ∈ frontier (s.projection ⁻¹' R)
    rw [← hvalue x]

open Classical in

theorem Step.exists_original_ordinary_double_graph
    {s t : Stage e S f r C} (step : Step s t) {R Fmark : Set M}
    {base : Fmark} {Jgroup : Subgroup (FundamentalGroup Fmark base)}
    (new : StageMarkedDisk t R Fmark base Jgroup)
    (hD2 : ∀ x ∈ D, ∀ y ∈ D, x ≠ y →
      step.projection (step.inclusion (new.map x)) =
        step.projection (step.inclusion (new.map y)) →
      ∃ (w : TwoBranchWindow (step.projection ∘ step.inclusion))
        (T : OpenPartialHomeomorph s.Carrier V3),
        ((new.map x ∈ w.left.source ∧ new.map y ∈ w.right.source) ∨
          (new.map x ∈ w.right.source ∧ new.map y ∈ w.left.source)) ∧
        step.projection (step.inclusion (new.map x)) ∈ T.source ∧
        T.source ⊆ w.target ∧
        (∀ k, (s.charts k).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
        (∀ z ∈ T.source,
          z ∈ (step.projection ∘ step.inclusion) '' (new.map '' D ∩ w.left.source) ↔
            T z 0 = 0 ∧ z ∈ s.projection ⁻¹' R) ∧
        (∀ z ∈ T.source,
          z ∈ (step.projection ∘ step.inclusion) '' (new.map '' D ∩ w.right.source) ↔
            T z 1 = 0 ∧ z ∈ s.projection ⁻¹' R) ∧
        (T.source ⊆ interior (s.projection ⁻¹' R) ∨
          ((∀ z ∈ T.source, z ∈ s.projection ⁻¹' R ↔ 0 ≤ T z 2) ∧
            ∀ z ∈ T.source, z ∈ frontier (s.projection ⁻¹' R) ↔ T z 2 = 0))) :
    ∃ (G : SimplicialComplex ℝ V2) (partner : G.space ≃ₜ G.space),
      G.faces.Finite ∧
      G.space = {x | x ∈ D ∧ ∃ y ∈ D, x ≠ y ∧
        step.projection (step.inclusion (new.map x)) =
          step.projection (step.inclusion (new.map y))} ∧
      partner.IsFinitePL ∧ partner.symm.IsFinitePL ∧
      Function.Involutive partner ∧ (∀ x : G.space, partner x ≠ x) ∧
      (∀ x : G.space,
        step.projection (step.inclusion (new.map x)) =
          step.projection (step.inclusion (new.map (partner x)))) ∧
      (∀ (x : G.space) (y : V2), y ∈ D → (x : V2) ≠ y →
        step.projection (step.inclusion (new.map x)) =
          step.projection (step.inclusion (new.map y)) → y = (partner x : V2)) ∧
      (∀ x : G.space, (partner x : V2) ∈ Rim ↔ (x : V2) ∈ Rim) ∧
      (∀ x ∈ G.space, ∃ u v : V2, u ≠ x ∧ v ≠ x ∧
        (x ∈ Rim → u = v) ∧
        (x ∉ Rim → segment ℝ x u ∩ segment ℝ x v ⊆ {x}) ∧
        ∀ᶠ z in 𝓝 x, z ∈ G.space ↔ z ∈ segment ℝ x u ∪ segment ℝ x v) ∧
      (∀ a ∈ G.faces, a.card ≤ 2) ∧
      (∀ v : G.vertices, (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard =
        if (v : V2) ∈ Rim then 1 else 2) ∧
      G.space ∩ Rim = (Subtype.val : G.vertices → V2) ''
        {v | (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1} := by
  classical
  obtain ⟨_L, G, _first, partner, _hL, hG, _hLs, hGs, _hfirst, _hfirstinv,
    _hfirstval, hpartner, hpartnerinv, _hpartnerval, hinvolution, hnoFixed,
    hvalue, hunique, hrim⟩ := step.exists_original_double_partner new
  suffices hgerms : ∀ x ∈ G.space, ∃ u v : V2, u ≠ x ∧ v ≠ x ∧
      (x ∈ Rim → u = v) ∧
      (x ∉ Rim → segment ℝ x u ∩ segment ℝ x v ⊆ {x}) ∧
      ∀ᶠ z in 𝓝 x, z ∈ G.space ↔ z ∈ segment ℝ x u ∪ segment ℝ x v by
    have hlocal (x : G.space) : ∃ U : Set V2, IsOpen U ∧ (x : V2) ∈ U ∧
        ∃ F : Finset (AffineSubspace ℝ V2),
          (∀ A ∈ F, Module.finrank ℝ A.direction ≤ 1) ∧
          ∀ z ∈ G.space ∩ U, ∃ A ∈ F, z ∈ A := by
      obtain ⟨u, v, _hu, _hv, _hboundary, _hinter, hnear⟩ := hgerms x x.property
      obtain ⟨U, hUsub, hU, hxU⟩ := _root_.mem_nhds_iff.mp hnear
      refine ⟨U, hU, hxU, {affineSpan ℝ ({(x : V2), u} : Set V2),
        affineSpan ℝ ({(x : V2), v} : Set V2)}, ?_, ?_⟩
      · intro A hA
        simp only [Finset.mem_insert, Finset.mem_singleton] at hA
        rcases hA with rfl | rfl <;> rw [direction_affineSpan]
        · exact (collinear_pair ℝ (x : V2) u).finrank_le_one
        · exact (collinear_pair ℝ (x : V2) v).finrank_le_one
      · intro z hz
        rcases (hUsub hz.2).mp hz.1 with hzu | hzv
        · exact ⟨_, Finset.mem_insert_self _ _,
            convexHull_subset_affineSpan _ (by simpa only [convexHull_pair] using hzu)⟩
        · exact ⟨_, Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
            convexHull_subset_affineSpan _ (by simpa only [convexHull_pair] using hzv)⟩
    choose U hU hxU F hFdim hFcover using hlocal
    obtain ⟨I, hI⟩ := (G.isCompact_space_of_finite hG).elim_finite_subcover U hU
      (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩)
    let cover := I.biUnion F
    have hdim : ∀ A ∈ cover, Module.finrank ℝ A.direction ≤ 1 := by
      intro A hA
      obtain ⟨x, _hx, hAF⟩ := Finset.mem_biUnion.mp hA
      exact hFdim x A hAF
    have hcover : ∀ x ∈ G.space, ∃ A ∈ cover, x ∈ A := by
      intro x hx
      obtain ⟨z, hzI, hxU⟩ := mem_iUnion₂.mp (hI hx)
      obtain ⟨A, hA, hxA⟩ := hFcover z x ⟨hx, hxU⟩
      exact ⟨A, Finset.mem_biUnion.mpr ⟨z, hzI, hA⟩, hxA⟩
    have hcard : ∀ a ∈ G.faces, a.card ≤ 2 :=
      fun _ ha => G.face_card_le_of_finite_affine_cover cover hdim hcover ha
    have hlinkspace (v : G.vertices) : (G.link (v : V2)).space =
        (G.faceLink {(v : V2)}).vertices := by
      rw [← G.faceLink_singleton_eq_link]
      apply subset_antisymm
      · intro z hz
        obtain ⟨a, ha, hza⟩ := SimplicialComplex.mem_space_iff.mp hz
        have hbound := G.card_add_card_le_of_mem_faceLink hcard {(v : V2)} ha
        have hpos := Finset.card_pos.mpr ((G.faceLink {(v : V2)}).nonempty_of_mem_faces ha)
        simp only [Finset.card_singleton] at hbound
        obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp (show a.card = 1 by omega)
        have hza' : z = a := by
          simpa only [Finset.coe_singleton, convexHull_singleton, Set.mem_singleton_iff] using hza
        exact hza'.symm ▸ ha
      · exact (G.faceLink {(v : V2)}).vertices_subset_space
    have hdegree (v : G.vertices) :
        (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard =
          if (v : V2) ∈ Rim then 1 else 2 := by
      obtain ⟨u, w, hu, hw, hboundary, hinter, hnear⟩ :=
        hgerms v (G.vertices_subset_space v.property)
      let e : V2 ≃ᴬ[ℝ] V2 := ContinuousAffineEquiv.constVAdd ℝ V2 (-(v : V2))
      have he0 : e v = 0 := by change -(v : V2) + v = 0; exact neg_add_cancel _
      have hei0 : e.symm 0 = (v : V2) := e.injective (by rw [e.apply_symm_apply, he0])
      let hf := G.affineOnFaces_affine e.toContinuousAffineMap
      let J := hf.embeddedImage e.injective.injOn
      have hJ := hf.embeddedImage_finite e.injective.injOn hG
      have hJs : J.space = e '' G.space := hf.embeddedImage_space e.injective.injOn
      have hJv : (0 : V2) ∈ J.vertices := by
        rw [hf.embeddedImage_vertices e.injective.injOn]
        exact ⟨v, v.property, he0⟩
      have hJl : (J.link 0).space = e '' (G.link (v : V2)).space := by
        have h := hf.embeddedImage_link_space e.injective.injOn v.property
        change (J.link (e v)).space = e '' (G.link (v : V2)).space at h
        simpa only [he0] using h
      have hcount : (J.link 0).space.ncard =
          (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard := by
        rw [hJl, ncard_image_of_injective _ e.injective, hlinkspace,
          G.ncard_edgeGraph_neighborSet]
      have hseg (a : V2) : e '' segment ℝ (v : V2) a = segment ℝ 0 (e a) := by
        have h := image_segment ℝ e.toAffineEquiv.toAffineMap (v : V2) a
        change e '' segment ℝ (v : V2) a = segment ℝ (e v) (e a) at h
        simpa only [he0] using h
      have hpre (S : Set V2) (z : V2) : e.symm z ∈ S ↔ z ∈ e '' S := by
        constructor
        · intro hz
          exact ⟨e.symm z, hz, e.apply_symm_apply z⟩
        · rintro ⟨a, ha, rfl⟩
          simpa only [e.symm_apply_apply] using ha
      have hnearJ : ∀ᶠ z in 𝓝 (0 : V2),
          z ∈ J.space ∩ {a | (0 : V2 →ₗ[ℝ] ℝ) a = 0} ↔
            z ∈ segment ℝ 0 (e u) ∪ segment ℝ 0 (e w) := by
        have htend : Tendsto e.symm (𝓝 (0 : V2)) (𝓝 (v : V2)) := by
          simpa only [hei0] using e.symm.continuous.tendsto 0
        have h := htend.eventually hnear
        filter_upwards [h] with z hz
        simp only [LinearMap.zero_apply, Set.ofPred_true, inter_univ]
        rw [hJs, ← hseg u, ← hseg w, ← image_union, ← hpre, ← hpre]
        exact hz
      have heu : e u ≠ 0 := fun h => hu (e.injective (h.trans he0.symm))
      have hew : e w ≠ 0 := fun h => hw (e.injective (h.trans he0.symm))
      by_cases hvR : (v : V2) ∈ Rim
      · rw [if_pos hvR, ← hcount]
        have hn := J.normalize_image_link_zero_of_local_segments hJ hJv
          (0 : V2 →ₗ[ℝ] ℝ) heu hew hnearJ
        simp only [LinearMap.zero_apply, Set.ofPred_true, inter_univ, hboundary hvR,
          Set.pair_eq_singleton] at hn
        rw [← J.injOn_normalize_link.ncard_image, hn, ncard_singleton]
      · rw [if_neg hvR, ← hcount]
        have hinterJ : segment ℝ 0 (e u) ∩ segment ℝ 0 (e w) ⊆ {0} := by
          rw [← hseg u, ← hseg w, ← image_inter e.injective]
          rintro z ⟨a, ha, rfl⟩
          exact (congrArg e (hinter hvR ha)).trans he0
        simpa only [LinearMap.zero_apply, Set.ofPred_true, inter_univ] using
          J.ncard_link_zero_of_local_segments hJ hJv (0 : V2 →ₗ[ℝ] ℝ)
            heu hew hinterJ hnearJ
    have hrimvertex : G.space ∩ Rim ⊆ G.vertices := by
      intro x hx
      by_contra hxv
      obtain ⟨a, ha, hxa⟩ := G.exists_face_intrinsicInterior_of_finite hG hx.1
      have ha2 : a.card = 2 := by
        have hpos := Finset.card_pos.mpr (G.nonempty_of_mem_faces ha)
        have hbound := hcard a ha
        by_contra hn
        have hone : a.card = 1 := by omega
        obtain ⟨q, rfl⟩ := Finset.card_eq_one.mp hone
        have hxq : x = q := by
          simpa only [Finset.coe_singleton, convexHull_singleton, Set.mem_singleton_iff]
            using intrinsicInterior_subset hxa
        exact hxv (hxq.symm ▸ ha)
      have hmax : ∀ b ∈ G.faces, a ⊆ b → b = a := by
        intro b hb hab
        exact (Finset.eq_of_subset_of_card_le hab (by rw [ha2]; exact hcard b hb)).symm
      obtain ⟨U, hU, hxU, hUg⟩ := G.exists_open_maximal_face_affine_germ hG ha hmax hxa
      obtain ⟨u, v, hu, _hv, hboundary, _hinter, hnear⟩ := hgerms x hx.1
      rw [← hboundary hx.2, union_self] at hnear
      obtain ⟨q, hqa⟩ := G.nonempty_of_mem_faces ha
      have hqx : q ≠ x := fun h => hxv (h ▸ G.face_subset_vertices ha hqa)
      have hxspan : x ∈ affineSpan ℝ (a : Set V2) :=
        convexHull_subset_affineSpan _ (intrinsicInterior_subset hxa)
      have hqspan : q ∈ affineSpan ℝ (a : Set V2) := subset_affineSpan ℝ _ hqa
      let A : ℝ →ᴬ[ℝ] V2 := ContinuousAffineMap.lineMap x q
      have hA0 : A 0 = x := AffineMap.lineMap_apply_zero _ _
      have hn : {r : ℝ | A r ∈ U ∧ (A r ∈ G.space ↔ A r ∈ segment ℝ x u) ∧
          A (-r) ∈ U ∧ (A (-r) ∈ G.space ↔ A (-r) ∈ segment ℝ x u)} ∈ 𝓝 0 := by
        have hnearU : ∀ᶠ z in 𝓝 x, z ∈ U ∧
            (z ∈ G.space ↔ z ∈ segment ℝ x u) := by
          filter_upwards [hU.mem_nhds hxU, hnear] with z hzU hz
          exact ⟨hzU, hz⟩
        have hp : Tendsto A (𝓝 (0 : ℝ)) (𝓝 x) := by
          simpa only [hA0] using A.continuous.tendsto 0
        have hm : Tendsto (fun r : ℝ => A (-r)) (𝓝 0) (𝓝 x) := by
          change Tendsto (A ∘ fun r : ℝ => -r) (𝓝 0) (𝓝 x)
          exact hp.comp (by simpa only [neg_zero] using
            (continuous_neg : Continuous (fun r : ℝ => -r)).tendsto 0)
        filter_upwards [hp.eventually hnearU, hm.eventually hnearU] with r hr hr'
        exact ⟨hr.1, hr.2, hr'.1, hr'.2⟩
      obtain ⟨r, hr, hn⟩ := Set.exists_pos_smul_mem_of_mem_nhds hn (1 : ℝ)
      simp only [smul_eq_mul, mul_one] at hn
      have hpseg := hn.2.1.mp ((hUg _ hn.1).mpr (AffineMap.lineMap_mem r hxspan hqspan))
      have hmseg := hn.2.2.2.mp ((hUg _ hn.2.2.1).mpr
        (AffineMap.lineMap_mem (-r) hxspan hqspan))
      obtain ⟨α, β, _hα, hβ, hab, heq⟩ := hpseg
      obtain ⟨γ, δ, _hγ, hδ, hgd, heq'⟩ := hmseg
      have hp : β • (u - x) = r • (q - x) := by
        change α • x + β • u = AffineMap.lineMap x q r at heq
        rw [AffineMap.lineMap_apply_module'] at heq
        ext i
        have hi := congrFun heq i
        have hsum := congrArg (fun t : ℝ => t * x i) hab
        simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hi ⊢
        nlinarith
      have hm : δ • (u - x) = (-r) • (q - x) := by
        change γ • x + δ • u = AffineMap.lineMap x q (-r) at heq'
        rw [AffineMap.lineMap_apply_module'] at heq'
        ext i
        have hi := congrFun heq' i
        have hsum := congrArg (fun t : ℝ => t * x i) hgd
        simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hi ⊢
        nlinarith
      have hsum : (β + δ) • (u - x) = 0 := by rw [add_smul, hp, hm]; module
      have hcoef := (smul_eq_zero.mp hsum).resolve_right (sub_ne_zero.mpr hu)
      have hβ0 : β = 0 := by linarith
      exact (smul_ne_zero hr.1.ne' (sub_ne_zero.mpr hqx))
        (by simpa only [hβ0, zero_smul] using hp.symm)
    refine ⟨G, partner, hG, hGs, hpartner, hpartnerinv, hinvolution, hnoFixed,
      hvalue, hunique, hrim, hgerms, hcard, hdegree, ?_⟩
    ext x
    constructor
    · intro hx
      let v : G.vertices := ⟨x, hrimvertex hx⟩
      refine ⟨v, ?_, rfl⟩
      change (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1
      rw [hdegree, if_pos hx.2]
    · rintro ⟨v, hv, rfl⟩
      refine ⟨G.vertices_subset_space v.property, ?_⟩
      by_contra hn
      change (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1 at hv
      rw [hdegree, if_neg hn] at hv
      omega
  intro x hxG
  obtain ⟨hxD, y, hyD, hxy, hxyval⟩ := hGs.subset hxG
  obtain ⟨w, T, _hlabels, hxT, hTw, hTPL, hleft, hright, hregion⟩ :=
    hD2 x hxD y hyD hxy hxyval
  let p := step.projection ∘ step.inclusion
  let lower := p ∘ new.map
  have hinside {z : V2} (hz : z ∈ D) : lower z ∈ s.projection ⁻¹' R :=
    (step.region_preimage R).subset (new.inside hz)
  have hproper {z : V2} (hz : z ∈ D) :
      lower z ∈ frontier (s.projection ⁻¹' R) ↔ z ∈ Rim := by
    have h := new.whole_boundary_iff ⟨z, hz⟩
    rw [step.frontier_preimage R] at h
    exact h
  have hinj : InjOn new.map D := by
    intro a ha b hb hab
    have h : (⟨a, ha⟩ : D) = ⟨b, hb⟩ := new.embedding.injective hab
    exact congrArg Subtype.val h
  have hcross {a b : V2} (ha : a ∈ D) (hb : b ∈ D) (hne : a ≠ b)
      (heq : lower a = lower b) (haT : lower a ∈ T.source) :
      lower a ∈ p '' (new.map '' D ∩ w.left.source) ∧
        lower a ∈ p '' (new.map '' D ∩ w.right.source) := by
    have haW := w.whole_preimage.subset (hTw haT)
    have hbW := w.whole_preimage.subset (heq ▸ hTw haT)
    rcases haW with haL | haR <;> rcases hbW with hbL | hbR
    · exact (hne (hinj ha hb (w.left.injOn haL hbL (by
        simpa only [w.left_eq, lower, p, Function.comp_apply] using heq)))).elim
    · exact ⟨⟨new.map a, ⟨mem_image_of_mem _ ha, haL⟩, rfl⟩,
        ⟨new.map b, ⟨mem_image_of_mem _ hb, hbR⟩, heq.symm⟩⟩
    · exact ⟨⟨new.map b, ⟨mem_image_of_mem _ hb, hbL⟩, heq.symm⟩,
        ⟨new.map a, ⟨mem_image_of_mem _ ha, haR⟩, rfl⟩⟩
    · exact (hne (hinj ha hb (w.right.injOn haR hbR (by
        simpa only [w.right_eq, lower, p, Function.comp_apply] using heq)))).elim
  have hfull {z : V2} (hzD : z ∈ D) (hzT : lower z ∈ T.source) :
      z ∈ G.space ↔ T (lower z) 0 = 0 ∧ T (lower z) 1 = 0 := by
    constructor
    · intro hzG
      obtain ⟨_, v, hvD, hzv, hsame⟩ := hGs.subset hzG
      have hboth := hcross hzD hvD hzv hsame hzT
      exact ⟨((hleft _ hzT).mp hboth.1).1, ((hright _ hzT).mp hboth.2).1⟩
    · rintro ⟨hz0, hz1⟩
      obtain ⟨a, ⟨⟨u, hu, rfl⟩, huL⟩, huval⟩ :=
        (hleft _ hzT).mpr ⟨hz0, hinside hzD⟩
      obtain ⟨b, ⟨⟨v, hv, rfl⟩, hvR⟩, hvval⟩ :=
        (hright _ hzT).mpr ⟨hz1, hinside hzD⟩
      by_cases hzu : z = u
      · apply hGs.symm.subset
        refine ⟨hzD, v, hv, ?_, hvval.symm⟩
        intro hzv
        exact w.disjoint.ne_of_mem huL hvR (congrArg new.map (hzu.symm.trans hzv))
      · exact hGs.symm.subset ⟨hzD, u, hu, hzu, huval.symm⟩
  have hxaxis := (hfull hxD hxT).mp hxG
  obtain ⟨B, hBx, hBp, hBt, hBaxis⟩ :
      ∃ B : OpenPartialHomeomorph t.Carrier s.Carrier,
        new.map x ∈ B.source ∧ (B : t.Carrier → s.Carrier) = p ∧ B.target = w.target ∧
        ∀ z ∈ T.source, T z 0 = 0 → T z 1 = 0 → z ∈ s.projection ⁻¹' R →
          z ∈ p '' (new.map '' D ∩ B.source) := by
    rcases w.whole_preimage.subset (hTw hxT) with hxL | hxR
    · exact ⟨w.left, hxL, w.left_eq, w.left_target,
        fun z hz h0 _ hR => (hleft z hz).mpr ⟨h0, hR⟩⟩
    · exact ⟨w.right, hxR, w.right_eq, w.right_target,
        fun z hz _ h1 hR => (hright z hz).mpr ⟨h1, hR⟩⟩
  let Q := B.trans T
  have hQval (z : t.Carrier) : Q z = T (p z) := congrArg T (congrFun hBp z)
  have hQsource (z : t.Carrier) :
      z ∈ Q.source ↔ z ∈ B.source ∧ p z ∈ T.source := by
    change (z ∈ B.source ∧ B z ∈ T.source) ↔ _
    rw [congrFun hBp z]
  have hxQ : new.map x ∈ Q.source := (hQsource _).mpr ⟨hBx, hxT⟩
  have hQt : Q.target = T.target := by
    apply subset_antisymm inter_subset_left
    intro z hz
    exact ⟨hz, hBt.symm.subset (hTw (T.map_target hz))⟩
  have hQPL (k : t.Index) : (t.charts k).symm.trans Q ∈ piecewiseAffineGroupoid V3 := by
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    intro z hz
    obtain ⟨l, hl⟩ := s.cover (B ((t.charts k).symm z))
    let F := (t.charts k).symm.trans (B.trans (s.charts l))
    let H := (s.charts l).symm.trans T
    have hF : F ∈ piecewiseAffineGroupoid V3 := step.branch_chart_PL B
      (fun a _ => congrFun hBp a) k l
    have hzF : z ∈ F.source := ⟨hz.1, hz.2.1, hl⟩
    have hzH : F z ∈ H.source := by
      refine ⟨(s.charts l).map_source hl, ?_⟩
      change (s.charts l).symm ((s.charts l) (B ((t.charts k).symm z))) ∈ T.source
      rw [(s.charts l).left_inv hl]
      exact hz.2.2
    obtain ⟨U, hU, hzU, hUF, hUH⟩ := (hTPL l).1.comp hF.1 z ⟨hzF, hzH⟩
    refine ⟨U, hU, hzU, ?_, ?_⟩
    · intro a ha
      have hf := (hUF ha).1
      exact ⟨hf.1, hf.2.1,
        (congrArg (fun b => b ∈ T.source) ((s.charts l).left_inv hf.2.2)).mp (hUF ha).2.2⟩
    · apply hUH.congr
      intro a ha
      exact congrArg T ((s.charts l).left_inv (hUF ha).1.2.2)
  obtain ⟨K, hK, hKs⟩ := SimplicialComplex.exists_finite_coordinate_closedBall
    (0 : V2) (r := 1) zero_le_one
  obtain ⟨r₀, J, hr₀, hJ, hJs, hJQ, _hsmall, _hmargin⟩ :=
    SimplicialComplex.exists_nested_finite_coordinate_cubes Q.open_target (Q.map_source hxQ)
  have hxJ : Q (new.map x) ∈ interior J.space := by
    rw [hJs]
    exact ball_subset_interior_closedBall (mem_ball_self (by positivity))
  have hj : PolyhedralPLInCharts t.charts new.map K.space := by
    simpa only [hKs] using new.piecewiseAffine
  obtain ⟨N, q, _hN, hNs, hq, hqD, hqright, hqleft⟩ :=
    hj.exists_finite_clipped_chart_inverse K hK (by simpa only [hKs] using hinj)
      Q hQPL J hJ hJQ
  let axis : ℝ →ᴬ[ℝ] V3 := (ContinuousLinearMap.pi fun i : Fin 3 =>
    if i = 2 then ContinuousLinearMap.id ℝ ℝ else 0).toContinuousAffineMap
  have haxis (u : ℝ) (i : Fin 3) : axis u i = if i = 2 then u else 0 := by
    by_cases hi : i = 2 <;> simp [axis, hi]
  have haxisback {z : V3} (hz0 : z 0 = 0) (hz1 : z 1 = 0) : axis (z 2) = z := by
    ext i
    fin_cases i <;> simp [haxis, hz0, hz1]
  let t₀ := T (lower x) 2
  have hat : axis t₀ = Q (new.map x) := by rw [hQval]; exact haxisback hxaxis.1 hxaxis.2
  have hxinterior : x ∉ Rim → lower x ∈ interior (s.projection ⁻¹' R) := by
    intro hxrim
    by_contra hout
    exact hxrim ((hproper hxD).mp ⟨subset_closure (hinside hxD), hout⟩)
  have hboundary : x ∈ Rim → t₀ = 0 ∧
      ∀ z ∈ T.source, z ∈ s.projection ⁻¹' R ↔ 0 ≤ T z 2 := by
    intro hxrim
    rcases hregion with hI | ⟨hR, hF⟩
    · exact False.elim (((hproper hxD).mpr hxrim).2 (hI hxT))
    · exact ⟨(hF _ hxT).mp ((hproper hxD).mpr hxrim), hR⟩
  let O : Set V3 := interior J.space ∩
    (if x ∈ Rim then univ else T.target ∩ T.symm ⁻¹' interior (s.projection ⁻¹' R))
  have hO : IsOpen O := isOpen_interior.inter (by
    split_ifs
    · exact isOpen_univ
    · exact T.isOpen_inter_preimage_symm isOpen_interior)
  have hatO : axis t₀ ∈ O := by
    refine ⟨hat.symm ▸ hxJ, ?_⟩
    by_cases hxrim : x ∈ Rim
    · simp only [hxrim, if_pos, mem_univ]
    · simp only [if_neg hxrim]
      rw [hat, hQval]
      refine ⟨T.map_source hxT, ?_⟩
      change T.symm (T (lower x)) ∈ interior (s.projection ⁻¹' R)
      have hinv : T.symm (T (lower x)) = lower x :=
        T.left_inv (show lower x ∈ T.source from hxT)
      rw [hinv]
      exact hxinterior hxrim
  obtain ⟨ε₀, hε₀, hεO⟩ := Metric.isOpen_iff.mp (hO.preimage axis.continuous) t₀ hatO
  let ε := ε₀ / 2
  have hε : 0 < ε := half_pos hε₀
  let dir : Bool → ℝ := fun b => if b = true ∧ x ∉ Rim then -1 else 1
  have hdir (b : Bool) : |dir b| = 1 := by
    dsimp only [dir]
    split_ifs <;> norm_num
  have hdir0 : dir false = 1 := by
    simp only [dir, Bool.false_eq_true, false_and, if_false]
  let a : Bool → ℝ →ᴬ[ℝ] V3 := fun b => axis.comp
    (ContinuousAffineMap.const ℝ ℝ t₀ + (dir b * ε) • ContinuousAffineMap.id ℝ ℝ)
  have ha (b : Bool) (u : ℝ) : a b u = axis (t₀ + dir b * ε * u) := rfl
  have ha0 (b : Bool) : a b 0 = Q (new.map x) := by rw [ha]; simpa using hat
  have haO (b : Bool) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : a b u ∈ O := by
    apply hεO
    change dist (t₀ + dir b * ε * u) t₀ < ε₀
    rw [Real.dist_eq, add_sub_cancel_left, abs_mul, abs_mul, hdir,
      abs_of_pos hε, abs_of_nonneg hu.1, one_mul]
    have : ε * u ≤ ε := by nlinarith [hu.2]
    exact this.trans_lt (by dsimp only [ε]; linarith)
  have haN (b : Bool) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : a b u ∈ N.space := by
    have hJmem := interior_subset (haO b hu).1
    have ht : a b u ∈ T.target := hQt.subset (hJQ hJmem)
    have hsource := T.map_target ht
    have hR : T.symm (a b u) ∈ s.projection ⁻¹' R := by
      by_cases hxrim : x ∈ Rim
      · apply ((hboundary hxrim).2 _ hsource).mpr
        rw [T.right_inv ht, ha, haxis]
        simp only [ite_true, dir, hxrim, not_true_eq_false, and_false, if_false,
          (hboundary hxrim).1, zero_add, one_mul]
        exact mul_nonneg hε.le hu.1
      · have hz := (haO b hu).2
        simp only [if_neg hxrim] at hz
        exact interior_subset hz.2
    have hz0 : T (T.symm (a b u)) 0 = 0 := by
      rw [T.right_inv ht, ha, haxis, if_neg (by decide : (0 : Fin 3) ≠ 2)]
    have hz1 : T (T.symm (a b u)) 1 = 0 := by
      rw [T.right_inv ht, ha, haxis, if_neg (by decide : (1 : Fin 3) ≠ 2)]
    obtain ⟨v, ⟨⟨z, hzD, rfl⟩, hzB⟩, hval⟩ := hBaxis _ hsource hz0 hz1 hR
    have hzQ : new.map z ∈ Q.source := (hQsource _).mpr
      ⟨hzB, (congrArg (fun v => v ∈ T.source) hval).mpr hsource⟩
    rw [hNs]
    refine ⟨⟨new.map z, ⟨mem_image_of_mem _ (hKs.symm.subset hzD), hzQ⟩, ?_⟩, hJmem⟩
    rw [hQval, hval, T.right_inv ht]
  have hqcoord (b : Bool) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
      Q (new.map (q (a b u))) = a b u := (hqright _ (haN b hu)).2
  have hqG (b : Bool) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : q (a b u) ∈ G.space := by
    have hzQ := (hqright _ (haN b hu)).1
    apply (hfull (hKs.subset (hqD (haN b hu))) ?_).mpr
    · change T (p (new.map (q (a b u)))) 0 = 0 ∧
        T (p (new.map (q (a b u)))) 1 = 0
      rw [← hQval, hqcoord b hu, ha]
      constructor
      · rw [haxis, if_neg (by decide : (0 : Fin 3) ≠ 2)]
      · rw [haxis, if_neg (by decide : (1 : Fin 3) ≠ 2)]
    · exact ((hQsource _).mp hzQ).2
  have hq0 (b : Bool) : q (a b 0) = x := by
    rw [ha0]
    exact hqleft x (hKs.symm.subset hxD) hxQ (interior_subset hxJ)
  choose ρ hρ A hA₀ using fun b : Bool =>
    hq.exists_initial_affine_segment (a b) (fun _ hu => haN b hu)
  let δ : Bool → ℝ := fun _ => min (ρ false) (ρ true)
  have hδρ (b : Bool) : δ b ≤ ρ b := by
    cases b
    · exact min_le_left _ _
    · exact min_le_right _ _
  have hδ (b : Bool) : δ b ∈ Ioc (0 : ℝ) 1 :=
    ⟨lt_min (hρ false).1 (hρ true).1, (hδρ b).trans (hρ b).2⟩
  have hA (b : Bool) : EqOn (q ∘ a b) (A b) (Icc 0 (δ b)) := by
    intro u hu
    exact hA₀ b (show u ∈ Icc 0 (ρ b) from ⟨hu.1, hu.2.trans (hδρ b)⟩)
  let endpoint (b : Bool) := q (a b (δ b))
  have hseg (b : Bool) : (q ∘ a b) '' Icc 0 (δ b) = segment ℝ x (endpoint b) := by
    calc
      (q ∘ a b) '' Icc 0 (δ b) = A b '' Icc 0 (δ b) := image_congr (hA b)
      _ = segment ℝ (A b 0) (A b (δ b)) := by
        rw [← segment_eq_Icc (hδ b).1.le]
        exact image_segment ℝ (A b).toAffineMap 0 (δ b)
      _ = segment ℝ x (endpoint b) := by
        rw [← hA b ⟨le_rfl, (hδ b).1.le⟩, ← hA b ⟨(hδ b).1.le, le_rfl⟩]
        change segment ℝ (q (a b 0)) (endpoint b) = segment ℝ x (endpoint b)
        rw [hq0]
  have hnonzero (b : Bool) : endpoint b ≠ x := by
    intro heq
    have hcoord := hqcoord b ⟨(hδ b).1.le, (hδ b).2⟩
    change Q (new.map (endpoint b)) = a b (δ b) at hcoord
    rw [heq, ← ha0 b] at hcoord
    have hscalar := congrArg (fun z : V3 => z 2) hcoord
    simp only [ha, haxis, ite_true, mul_zero, add_zero] at hscalar
    have hd : dir b ≠ 0 := by
      intro hd
      have hzeroone : (0 : ℝ) = 1 := by simpa only [hd, abs_zero] using hdir b
      exact zero_ne_one hzeroone
    exact (mul_ne_zero (mul_ne_zero hd hε.ne') (hδ b).1.ne') (by linarith)
  have hsegments (b : Bool) : segment ℝ x (endpoint b) ⊆ G.space := by
    rw [← hseg]
    rintro z ⟨u, hu, rfl⟩
    exact hqG b ⟨hu.1, hu.2.trans (hδ b).2⟩
  refine ⟨endpoint false, endpoint true, hnonzero false, hnonzero true, ?_, ?_, ?_⟩
  · intro hxrim
    have haeq : a true = a false := by
      ext u i
      simp only [ha, dir, hxrim, not_true_eq_false, and_false, if_false]
    change q (a false (δ false)) = q (a true (δ true))
    rw [haeq]
  · intro hxrim z hz
    obtain ⟨u, hu, hzu⟩ := (hseg false).symm.subset hz.1
    obtain ⟨v, hv, hzv⟩ := (hseg true).symm.subset hz.2
    dsimp only [Function.comp_apply] at hzu hzv
    have hcoords := congrArg (fun z => Q (new.map z)) (hzu.trans hzv.symm)
    rw [hqcoord false ⟨hu.1, hu.2.trans (hδ false).2⟩,
      hqcoord true ⟨hv.1, hv.2.trans (hδ true).2⟩] at hcoords
    have hscalar := congrArg (fun z : V3 => z 2) hcoords
    have hdir1 : dir true = -1 := if_pos ⟨rfl, hxrim⟩
    simp only [ha, haxis, ite_true, hdir0, hdir1, one_mul, neg_one_mul] at hscalar
    have hu0 : u = 0 := by nlinarith [hε, hu.1, hv.1]
    exact (hzu.symm.trans (hu0 ▸ hq0 false) : z = x)
  · let η := ε * min (δ false) (δ true)
    have hη : 0 < η := mul_pos hε (lt_min (hδ false).1 (hδ true).1)
    let V := Q.source ∩ Q ⁻¹' (interior J.space ∩
      {z : V3 | |z 2 - t₀| < η})
    have hV : IsOpen V := Q.isOpen_inter_preimage (isOpen_interior.inter
      (isOpen_lt (by fun_prop) continuous_const))
    have hxV : new.map x ∈ V := by
      refine ⟨hxQ, hxJ, ?_⟩
      change |Q (new.map x) 2 - t₀| < η
      rw [hQval]
      change |t₀ - t₀| < η
      simpa only [sub_self, abs_zero] using hη
    have hDV : IsOpen ((fun z : D => new.map z) ⁻¹' V) := hV.preimage new.embedding.continuous
    obtain ⟨U, hU, hUD⟩ := isOpen_induced_iff.mp hDV
    have hxU : x ∈ U := by
      have : (⟨x, hxD⟩ : D) ∈ (Subtype.val : D → V2) ⁻¹' U := hUD.symm.subset hxV
      exact this
    filter_upwards [hU.mem_nhds hxU] with z hzU
    constructor
    · intro hzG
      have hzD := (hGs.subset hzG).1
      have hzV : new.map z ∈ V := hUD.subset (show (⟨z, hzD⟩ : D) ∈
        (Subtype.val : D → V2) ⁻¹' U from hzU)
      have hzT : lower z ∈ T.source := ((hQsource _).mp hzV.1).2
      have hzaxis := (hfull hzD hzT).mp hzG
      let u := (Q (new.map z) 2 - t₀) / ε
      have habs : |Q (new.map z) 2 - t₀| < ε * min (δ false) (δ true) := hzV.2.2
      have hinverse : q (Q (new.map z)) = z :=
        hqleft z (hKs.symm.subset hzD) hzV.1 (interior_subset hzV.2.1)
      have haxisz : axis (Q (new.map z) 2) = Q (new.map z) := by
        rw [hQval]
        exact haxisback hzaxis.1 hzaxis.2
      by_cases hu : 0 ≤ u
      · apply Or.inl
        rw [← hseg false]
        have huδ : u ≤ δ false := by
          dsimp only [u]
          apply (div_le_iff₀ hε).mpr
          have := (le_abs_self (Q (new.map z) 2 - t₀)).trans habs.le
          nlinarith [min_le_left (δ false) (δ true)]
        refine ⟨u, ⟨hu, huδ⟩, ?_⟩
        change q (a false u) = z
        rw [ha]
        have heq : t₀ + dir false * ε * u = Q (new.map z) 2 := by
          rw [hdir0, one_mul]
          dsimp only [u]
          field_simp [hε.ne']
          ring
        rw [heq, haxisz, hinverse]
      · have hxrim : x ∉ Rim := by
          intro hxrim
          have hn := ((hboundary hxrim).2 _ hzT).mp (hinside hzD)
          apply hu
          dsimp only [u]
          rw [hQval, (hboundary hxrim).1, sub_zero]
          exact div_nonneg hn hε.le
        apply Or.inr
        rw [← hseg true]
        have huδ : -u ≤ δ true := by
          dsimp only [u]
          rw [← neg_div]
          apply (div_le_iff₀ hε).mpr
          have := (neg_le_abs (Q (new.map z) 2 - t₀)).trans habs.le
          nlinarith [min_le_right (δ false) (δ true)]
        refine ⟨-u, ⟨neg_nonneg.mpr (le_of_not_ge hu), huδ⟩, ?_⟩
        change q (a true (-u)) = z
        rw [ha]
        have heq : t₀ + dir true * ε * (-u) = Q (new.map z) 2 := by
          rw [show dir true = -1 from if_pos ⟨rfl, hxrim⟩]
          dsimp only [u]
          field_simp [hε.ne']
          ring
        rw [heq, haxisz, hinverse]
    · intro hz
      exact hz.elim (fun h => hsegments false h) (fun h => hsegments true h)

end Geometry.OriginalPLTower
