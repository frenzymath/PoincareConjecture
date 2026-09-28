import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.ExtendedFamily
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.FlattenedChart
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.Composition.CommonRefinement
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.Composition.SupportStars
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.Composition.LocalImages
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.Composition.CofaceTransport



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_finite_cut_coface_position
    {D X ι : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S T : Set X}
    (hcover : ∀ y, ∃ i, y ∈ (e i).source)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K : SimplicialComplex ℝ D) (hK : K.faces.Finite)
    {g : D → X} (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (P : Set D) (hPK : P ⊆ K.space) (hfinite : (P ∩ g ⁻¹' S).Finite)
    (hcharts : ∀ x ∈ P, g x ∈ S → Nonempty (OriginalSurfacePairChart e S T (g x) false))
    {U : Set X} (hU : IsOpen U) (hPU : g '' (P ∩ g ⁻¹' S) ⊆ U) :
    ∃ (N : SimplicialComplex ℝ D) (F : X ≃ₜ X) (A : Set X),
      N.faces.Finite ∧ N.IsSubdivision K ∧ IsCompact A ∧ A ⊆ U ∧ EqOn F id Aᶜ ∧
      (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧ F ⁻¹' T = T ∧
      Disjoint (F '' S) (g '' N.vertices ∩ g '' P) ∧
      ∀ a ∈ N.faces, a.card = 2 → convexHull ℝ (a : Set D) ⊆ P →
        (F '' S ∩ (g '' convexHull ℝ (a : Set D))).Finite ∧
          HasOriginalEdgeCofaceCharts e (F '' S) N g a := by
  classical
  let I := P ∩ g ⁻¹' S
  let : Fintype I := hfinite.fintype
  let C (x : I) := (hcharts x x.property.1 x.property.2).some
  obtain ⟨V, hV, hVdis⟩ := (hfinite.image g).t2_separation
  let U₀ (x : I) := V (g x) ∩ U
  have hU₀ (x : I) : IsOpen (U₀ x) := (hV (g x)).2.inter hU
  have hxU₀ (x : I) : g x ∈ U₀ x :=
    ⟨(hV (g x)).1, hPU (mem_image_of_mem g x.property)⟩
  have hUdis : Pairwise (fun x y : I => Disjoint (U₀ x) (U₀ y)) := by
    intro x y hxy
    exact (hVdis (mem_image_of_mem g x.property) (mem_image_of_mem g y.property)
      (fun h => hxy (Subtype.ext (hgi (hPK x.property.1) (hPK y.property.1) h)))).mono
        inter_subset_left inter_subset_left
  choose r J O A W hr hJ hJK hO hxO hOU hA hAO hW hxW hWO hAeq hWeq hfamily using
    fun x : I => exists_original_local_coface_motion_family he K hK hg hgi
      ⟨x, hPK x.property.1⟩ (C x) (hU₀ x) (hxU₀ x)
  have hOdis : Pairwise (fun x y => Disjoint (O x) (O y)) := by
    intro x y hxy
    exact (hUdis hxy).mono ((hOU x).trans inter_subset_left) ((hOU y).trans inter_subset_left)
  have hAU (i : I) : A i ⊆ U :=
    (hAO i).trans ((hOU i).trans (inter_subset_left.trans inter_subset_right))
  have hxA (i : I) : g i ∈ A i := by
    rw [hAeq i]
    let Q := (C i).chart.trans (C i).coordinates
    have hxQ : g i ∈ Q.source := ⟨(C i).center_source, (C i).center_coordinates⟩
    refine ⟨0, Metric.mem_closedBall_self (hr i).le, ?_⟩
    change Q.symm 0 = g i
    rw [← (C i).center_zero]
    exact Q.left_inv hxQ
  obtain ⟨M, hM, hMK, hMJ⟩ := CollarMesh.exists_common_subdivision_of_finite_family K hK
    Finset.univ J (fun i _ => hJ i) (fun i _ => hJK i)
  have hgM : ContinuousOn g M.space := hMK.space_eq.symm ▸ hg.continuousOn
  obtain ⟨N, hN, hNM, hstars⟩ := CollarMesh.exists_subdivision_cofaces_over_disjoint_supports
    M hM hgM A O (fun i => (hA i).isClosed) hO hAO hOdis
  have hNK := hNM.trans hMK
  choose c G hc hfix hPL hInv hT hsurface hcofaces havoid hnew hmarks using
    fun i : I => hfamily i N hN (hNM.trans (hMJ i (Finset.mem_univ i))) 1 zero_lt_one
  obtain ⟨F, Z, hZ, hZA, hFfix, hFG, hFPL, hFinv, hFmarks⟩ :=
    exists_disjoint_original_motions_composition hcover he Finset.univ O A G
      (fun i _ j _ hij => hOdis hij) (fun i _ => hA i) (fun i _ => hAO i)
      (fun i _ => hfix i) (fun i _ => hPL i) (fun i _ => hInv i)
  have hZA' : Z ⊆ ⋃ i, A i := by simpa only [Finset.mem_univ, iUnion_true] using hZA
  have hFG' (i : I) : EqOn F (G i) (O i) := hFG i (Finset.mem_univ i)
  have hGU (i : I) : G i ⁻¹' O i = O i :=
    (G i).injective.preimage_eq_self_of_eqOn_compl
      (fun y hy => hfix i (fun h => hy (hAO i h)))
  have hlocal (i : I) (y : X) (hy : y ∈ O i) : y ∈ F '' S ↔ y ∈ G i '' S :=
    image_mem_iff_of_eqOn_preserved_open F (G i) (hFG' i) (hGU i) hy
  have holdW : S ∩ g '' P ⊆ ⋃ i, W i := by
    rintro y ⟨hyS, x, hxP, rfl⟩
    exact mem_iUnion.mpr ⟨⟨x, hxP, hyS⟩, hxW ⟨x, hxP, hyS⟩⟩
  have holdA : S ∩ g '' P ⊆ ⋃ i, A i := by
    rintro y ⟨hyS, x, hxP, rfl⟩
    exact mem_iUnion.mpr ⟨⟨x, hxP, hyS⟩, hxA ⟨x, hxP, hyS⟩⟩
  have hnewA (i : I) : ((G i '' S) \ S) ⊆ A i := by
    rintro y ⟨hy, hyn⟩
    by_contra hn
    obtain ⟨x, hx, hxy⟩ := hy
    exact hyn (((G i).injective (hxy.trans (hfix i hn).symm)) ▸ hx)
  have hcovered := image_contacts_covered_after_local_motions F G O A W hZA' hAO
    hFfix hfix hFG' hnew holdW
  have hcoveredA := image_contacts_covered_after_local_motions F G O A A hZA' hAO
    hFfix hfix hFG' hnewA holdA
  have hvertices := image_vertices_avoided_after_local_motions F G O A W hAO hWO
    hfix hFG' hcovered havoid
  refine ⟨N, F, Z, hN, hNK, hZ, ?_, hFfix, hFPL, hFinv,
    hFmarks T (fun i _ => hT i), hvertices, ?_⟩
  · intro y hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hZA' hy)
    exact hAU i hi
  · intro a ha hcard haP
    by_cases hmeet : (F '' S ∩ (g '' convexHull ℝ (a : Set D))).Nonempty
    swap
    · have heq := Set.not_nonempty_iff_eq_empty.mp hmeet
      refine ⟨by rw [heq]; exact finite_empty, ?_⟩
      intro y hy
      simp only [heq, mem_empty_iff_false] at hy
    obtain ⟨y, hyS, x, hxa, hxy⟩ := hmeet
    have hyP : y ∈ g '' P := ⟨x, haP hxa, hxy⟩
    obtain ⟨i, hyA⟩ := mem_iUnion.mp (hcoveredA ⟨hyS, hyP⟩)
    have hmaps := hstars i a ha ⟨y, ⟨x, hxa, hxy⟩, hyA⟩
    obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp hcard
    have hpe : p ∈ convexHull ℝ (({p, q} : Finset D) : Set D) := subset_convexHull ℝ _ (by simp)
    have hqe : q ∈ convexHull ℝ (({p, q} : Finset D) : Set D) := subset_convexHull ℝ _ (by simp)
    have hpO := hmaps {p, q} ha (Subset.refl _) hpe
    have hqO := hmaps {p, q} ha (Subset.refl _) hqe
    have hpF : g p ∉ F '' S := fun h => disjoint_left.mp hvertices h
      ⟨mem_image_of_mem g (N.face_subset_vertices ha (by simp)), mem_image_of_mem g (haP hpe)⟩
    have hqF : g q ∉ F '' S := fun h => disjoint_left.mp hvertices h
      ⟨mem_image_of_mem g (N.face_subset_vertices ha (by simp)), mem_image_of_mem g (haP hqe)⟩
    have hpG : g p ∉ G i '' S := fun h => hpF ((hlocal i _ hpO).mpr h)
    have hqG : g q ∉ G i '' S := fun h => hqF ((hlocal i _ hqO).mpr h)
    obtain ⟨hfiniteG, hchartsG⟩ := finite_contacts_and_coface_charts_of_normal_graph
      (C i) (r i) (c i) (by simpa only [Bool.false_eq_true, false_implies, and_true] using hsurface i)
      N ha hpG hqG (by
        intro t ht hat
        exact ⟨fun z hz => (hOU i (hmaps t ht hat hz)).2,
          hcofaces i t ht (hmaps t ht hat)⟩)
    have hfiniteG' : (G i '' S ∩ (g '' convexHull ℝ (({p, q} : Finset D) : Set D))).Finite := by
      simpa only [Finset.coe_pair] using hfiniteG
    exact finite_contacts_and_coface_charts_congr_on_open hfiniteG' hchartsG (hO i)
      (by rintro z ⟨v, hv, rfl⟩; exact hmaps {p, q} ha (Subset.refl _) hv)
      (fun z hz => (hlocal i z hz).symm)

end PoincareConjecture.M76
