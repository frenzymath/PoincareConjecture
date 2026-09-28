import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothDomain.EmbeddingSupplement
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.SliceProjection
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.ContDiff.Extension
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothDomain.Embedding
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothDomain.FromEmbedding
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Chain.Truncation









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M]
  {g : RiemannianMetric 3 M}


theorem exists_height_sublevel_halfspace_chart (N : EpsilonNeck g)
    {K : Set M} {t : ℝ} {x : M} (hx : x ∈ N.carrier)
    (hK : ∀ y ∈ N.carrier, y ∈ K ↔ (N.coordinate_inverse y).2 ≤ t) :
    ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)),
      x ∈ e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target ∧
      e.IsImage K {y | 0 ≤ y 0} := by
  let f : M → ℝ := fun y => -(N.coordinate_inverse y).2
  have hf : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ f N.carrier :=
    (contMDiff_snd.comp_contMDiffOn N.coordinate_inverse_smooth).neg
  obtain ⟨F, hF, hFeq⟩ :=
    Poincare.Manifold.exists_contMDiff_eq_near N.carrier_open hf hx
  have hreg : Function.Surjective (mfderiv (𝓡 3) 𝓘(ℝ, ℝ) F x) := by
    rw [hFeq.mfderiv_eq]
    intro r
    let z := N.coordinate_inverse x
    let v : RoundCylinderTangent z := (0, -r)
    refine ⟨mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z v, ?_⟩
    have hinv := (N.coordinate_inverse_smooth.contMDiffAt
      (N.carrier_open.mem_nhds hx)).mdifferentiableAt (by simp)
    have hleft := N.coordinate_inverse_mfderiv_map_prod (N.coordinate_inverse_mem x hx) v
    rw [N.coordinate_map_coordinate_inverse hx] at hleft
    change mfderiv (𝓡 3) 𝓘(ℝ, ℝ) (-(Prod.snd ∘ N.coordinate_inverse)) x _ = r
    rw [mfderiv_neg, mfderiv_comp x mdifferentiableAt_snd hinv, mfderiv_snd]
    change -(mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N.coordinate_inverse x
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z v)).2 = r
    convert congrArg (fun w => -w.2) hleft using 1 <;>
      simp [z, v, TangentSpace]
  obtain ⟨e, hxe, he, hei, hefirst, _⟩ :=
    Poincare.Manifold.exists_normalized_regular_point_chart
      (n := 2) (by simp) hF x (-t) hreg
  obtain ⟨V, hVsub, hV, hxV⟩ :=
    mem_nhds_iff.mp (inter_mem (N.carrier_open.mem_nhds hx) hFeq)
  refine ⟨e.restrOpen V hV, ⟨hxe, hxV⟩,
    he.mono (fun y hy => hy.1), hei.mono (fun y hy => hy.1), ?_⟩
  intro y hy
  change 0 ≤ e y 0 ↔ y ∈ K
  rw [hefirst y hy.1, (hVsub hy.2).2, hK y (hVsub hy.2).1]
  change 0 ≤ -(N.coordinate_inverse y).2 - -t ↔ (N.coordinate_inverse y).2 ≤ t
  constructor <;> intro h <;> linarith



theorem nonempty_smoothDomain_of_height_sublevel (N : EpsilonNeck g)
    {K : Set M} {t : ℝ} (hcompact : IsCompact K)
    (hconnected : IsConnected (interior K))
    (hfront : frontier K ⊆ N.carrier) (hne : (frontier K).Nonempty)
    (hK : ∀ y ∈ N.carrier, y ∈ K ↔ (N.coordinate_inverse y).2 ≤ t) :
    Nonempty (Poincare.Manifold.SmoothDomain 3 (interior K)) := by
  have hcharts : ∀ a : K,
      ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)),
        (a : M) ∈ e.source ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target ∧
        e.IsImage K {y | 0 ≤ y 0} := by
    intro a
    by_cases ha : (a : M) ∈ interior K
    · obtain ⟨e, hae, he, hei, himg⟩ :=
        Poincare.Manifold.exists_interior_superlevel_halfspace_chart
          (E := EuclideanSpace ℝ (Fin 3)) (n := 2) (by simp)
          (f := fun _ : M => (1 : ℝ)) continuous_const 0 a.val (by norm_num)
      refine ⟨e.restrOpen (interior K) isOpen_interior, ⟨hae, ha⟩,
        he.mono (fun y hy => hy.1), hei.mono (fun y hy => hy.1), ?_⟩
      intro y hy
      exact iff_of_true ((himg hy.1).mpr (by norm_num)) (interior_subset hy.2)
    · exact N.exists_height_sublevel_halfspace_chart
        (hfront ⟨subset_closure a.property, ha⟩) hK
  choose amb hamb using hcharts
  obtain ⟨CS, rel, hsource, _, hman, hemb⟩ :=
    Poincare.Manifold.exists_smooth_embedding_of_halfspace_charts
      (n := 2) (by simp) K amb hamb
  let := CS
  let := hman
  have himage := Poincare.Manifold.image_interior_of_isSmoothEmbedding hemb
  have hcl : closure (interior K) = K := by
    rw [← himage, hcompact.isClosed.isClosedEmbedding_subtypeVal.closure_image_eq,
      (Poincare.Manifold.dense_manifoldInterior (I := 𝓡∂ 3) (M := K)).closure_eq,
      image_univ, Subtype.range_val]
  have hboundary : Subtype.val '' (𝓡∂ 3).boundary K = frontier K := by
    rw [← ModelWithCorners.compl_interior, compl_eq_univ_sdiff,
      image_sdiff Subtype.val_injective, image_univ, Subtype.range_val,
      himage, frontier, hcompact.isClosed.closure_eq]
  have hb : ((𝓡∂ 3).boundary K).Nonempty := by
    apply Set.Nonempty.of_image (f := Subtype.val)
    rwa [hboundary]
  have hopen : IsOpen (interior K) := isOpen_interior
  generalize hΩ : interior K = Ω at *
  cases hcl
  exact ⟨⟨hopen, hconnected, hcompact, CS, hman, hemb, himage, hb⟩⟩

end PoincareConjecture.EpsilonNeck

namespace PoincareConjecture.CapCertificate



theorem exists_finite_chain_smoothDomain_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ C : CapCertificate g, C.epsilon ≤ ε₀ →
        ∀ (H : ConnectedNeckCapCover g) (T : BalancedNeckChain g C.epsilon),
          C.IsOutgoingChain H T →
          ∀ b : ℤ, T.shape = .finite 0 b →
          ∀ t : ℝ, t ∈ Ioo (C.epsilon⁻¹ / 2) C.epsilon⁻¹ →
            let K := (C.carrier ∪ (T.unionOpen : Set M)) \
              (T.neck b).region t C.epsilon⁻¹
            Nonempty (Poincare.Manifold.SmoothDomain 3 (interior K)) := by
  obtain ⟨ε₀, hε₀, hsmall, htrunc⟩ := exists_finite_chain_truncation_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C hε H T hT b hshape t ht
  obtain ⟨hcompact, _, _, hfront, _, hconnected⟩ :=
    htrunc C hε H T hT b hshape t ht
  have hzero : 0 ≤ b := by
    have h := hT.zero_active
    simpa only [hshape, ChainShape.active, mem_Icc, le_refl, true_and] using h
  have hb : b ∈ T.shape.active := by
    simpa only [hshape, ChainShape.active, mem_Icc] using And.intro hzero (le_refl b)
  have he := T.epsilon_eq b hb
  have hR : 0 < C.epsilon⁻¹ := inv_pos.mpr C.epsilon_pos
  have htN : t ∈ Ioo (-(T.neck b).epsilon⁻¹) (T.neck b).epsilon⁻¹ := by
    rw [he]
    exact ⟨by linarith [ht.1], ht.2⟩
  apply (T.neck b).nonempty_smoothDomain_of_height_sublevel hcompact hconnected
  · rw [hfront]
    rintro _ ⟨q, rfl⟩
    exact (T.neck b).coordinate_map_mem ⟨mem_univ _, htN⟩
  · rw [hfront]
    exact range_nonempty _
  · intro y hy
    have hyA : y ∈ C.carrier ∪ (T.unionOpen : Set M) :=
      Or.inr (mem_iUnion.mpr ⟨⟨b, hb⟩, hy⟩)
    have hyt := ((T.neck b).coordinate_inverse_mem y hy).2.2
    rw [he] at hyt
    change (y ∈ C.carrier ∪ (T.unionOpen : Set M) ∧
      ¬ (y ∈ (T.neck b).carrier ∧ t < ((T.neck b).coordinate_inverse y).2 ∧
        ((T.neck b).coordinate_inverse y).2 < C.epsilon⁻¹)) ↔
      ((T.neck b).coordinate_inverse y).2 ≤ t
    simp only [hyA, hy, hyt, true_and, and_true, not_lt]

end PoincareConjecture.CapCertificate
